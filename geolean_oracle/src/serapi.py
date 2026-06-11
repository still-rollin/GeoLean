"""
Minimal SerAPI client. Drives a `sertop` subprocess over stdin/stdout,
sending S-expression commands and reading newline-delimited responses.

Designed for the narrow needs of geolean_oracle:
  * Add a Coq sentence and get its state id.
  * Exec a state id (running the sentence).
  * Receive Feedback messages emitted between/during Exec (Show Proof
    output, error messages, etc.).
  * Detect when the Add or Exec is Completed.
"""

from __future__ import annotations

import re
import subprocess
import threading
import queue
from dataclasses import dataclass, field


# ---------------------------------------------------------------------------
# Very small S-expression scanner. We don't build a tree — we just walk
# response lines and pull out the bits we care about with regexes anchored
# on known shapes.
# ---------------------------------------------------------------------------

_RE_ADDED = re.compile(r"\(Added\s+(\d+)\b")
_RE_COMPLETED = re.compile(r"\(Answer\s+(\d+)\s+Completed\)")
_RE_ACK = re.compile(r"\(Answer\s+(\d+)\s+Ack\)")
_RE_COQEXN = re.compile(r"\(Answer\s+(\d+)\(CoqExn")
_RE_FEEDBACK = re.compile(r"\(Feedback\(\(.*?span_id\s+(\d+).*?contents(.*)\)\)\s*$")
_RE_MESSAGE_STR = re.compile(r'\(str\s*"((?:[^"\\]|\\.)*)"\)')


@dataclass
class Response:
    """One sertop response line, classified."""
    raw: str
    kind: str                                # "ack" | "added" | "completed" | "exn" | "feedback" | "other"
    answer_id: int | None = None
    span_id: int | None = None
    message: str | None = None               # decoded text for Feedback Messages
    error: bool = False                      # True if Feedback level Error or CoqExn


def _decode_message_str(s: str) -> str:
    return s.encode("utf-8").decode("unicode_escape", errors="replace")


def _classify(line: str) -> Response:
    if m := _RE_COMPLETED.search(line):
        return Response(line, "completed", answer_id=int(m.group(1)))
    if m := _RE_ADDED.search(line):
        # span_id sits right after `Added <n>`
        return Response(line, "added", span_id=int(m.group(1)))
    if m := _RE_COQEXN.match(line):
        return Response(line, "exn", answer_id=int(m.group(1)), error=True)
    if m := _RE_ACK.search(line):
        return Response(line, "ack", answer_id=int(m.group(1)))
    if m := _RE_FEEDBACK.search(line):
        span_id = int(m.group(1))
        text = None
        is_err = "level Error" in line
        if msg := _RE_MESSAGE_STR.search(line):
            text = _decode_message_str(msg.group(1))
        return Response(line, "feedback", span_id=span_id, message=text, error=is_err)
    return Response(line, "other")


class SerAPI:
    """A long-lived sertop process, command-by-command driver."""

    def __init__(self, q_paths: list[tuple[str, str]] | None = None, timeout: float = 60.0):
        args = ["sertop"]
        for path, name in q_paths or []:
            args += ["-Q", f"{path},{name}"]
        self.proc = subprocess.Popen(
            args,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self.timeout = timeout
        self._counter = 0
        self._lines: queue.Queue[str] = queue.Queue()
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()

    # -- internals ---------------------------------------------------------

    def _read_loop(self) -> None:
        assert self.proc.stdout is not None
        for line in self.proc.stdout:
            self._lines.put(line.rstrip("\n"))
        self._lines.put("")  # sentinel: EOF

    def _next_id(self) -> int:
        self._counter += 1
        return self._counter

    def _send(self, sexp: str) -> None:
        assert self.proc.stdin is not None
        self.proc.stdin.write(sexp + "\n")
        self.proc.stdin.flush()

    def _collect_until_completed(self, answer_id: int) -> list[Response]:
        """Drain response lines until we see `(Answer N Completed)` for our N."""
        out: list[Response] = []
        import time
        deadline = time.monotonic() + self.timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"sertop timed out waiting for Answer {answer_id} Completed")
            try:
                line = self._lines.get(timeout=min(remaining, 1.0))
            except queue.Empty:
                continue
            if line == "":
                raise RuntimeError("sertop closed unexpectedly")
            resp = _classify(line)
            out.append(resp)
            if resp.kind == "completed" and resp.answer_id == answer_id:
                return out

    # -- high-level operations --------------------------------------------

    def add(self, sentence: str) -> tuple[list[int], list[Response]]:
        """
        Send one Add command. Returns (span_ids, all_responses).
        A single Add may produce multiple spans if `sentence` contains
        several Coq sentences. We keep them all.
        """
        cid = self._next_id()
        escaped = sentence.replace("\\", "\\\\").replace('"', '\\"')
        self._send(f'({cid} (Add () "{escaped}"))')
        responses = self._collect_until_completed(cid)
        for r in responses:
            if r.error:
                raise CoqError(f"sertop Add error: {r.raw}")
        span_ids = [r.span_id for r in responses if r.kind == "added" and r.span_id is not None]
        return span_ids, responses

    def exec(self, span_id: int) -> list[Response]:
        """Run state `span_id`. Returns all responses (including feedback)."""
        cid = self._next_id()
        self._send(f"({cid} (Exec {span_id}))")
        responses = self._collect_until_completed(cid)
        # Errors from execution show up as CoqExn responses or Error feedback
        for r in responses:
            if r.kind == "exn":
                raise CoqError(self._extract_exn_message(r.raw))
            if r.kind == "feedback" and r.error and r.message:
                raise CoqError(r.message)
        return responses

    def close(self) -> None:
        try:
            if self.proc.stdin and not self.proc.stdin.closed:
                self.proc.stdin.close()
        except OSError:
            pass
        try:
            self.proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.proc.kill()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    # -- helpers ----------------------------------------------------------

    @staticmethod
    def _extract_exn_message(raw: str) -> str:
        if m := _RE_MESSAGE_STR.search(raw):
            return _decode_message_str(m.group(1))
        return raw[:200]


class CoqError(RuntimeError):
    """Raised when sertop reports an error from Coq."""
