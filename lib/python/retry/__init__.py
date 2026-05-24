"""Generic transient-failure retry primitives.

Shared by the gh CLI wrapper (:mod:`lib.python.github`) and the Claude CLI
streaming runner (:mod:`lib.python.claude_cli_streaming`) so the bounded
exponential-backoff mechanism lives in one place rather than being
copy-pasted — the ``jscpd --threshold 0`` gate forbids the duplication.

Callers keep their own domain-specific marker lists — gh transport errors
versus Node/undici socket errors — and pass them to
:func:`contains_transient_marker`; this module owns only the matching and
the backoff schedule, not the policy for what counts as transient.
"""

import random
import time

DEFAULT_MAX_ATTEMPTS = 10

_rng = random.Random()


def contains_transient_marker(text: str, substrings: tuple[str, ...]) -> bool:
    """Return True when any of *substrings* appears in *text*.

    Case-insensitive substring match. Carries no return-code gating of
    its own; the caller decides when to consult it.
    """
    lower = text.lower()
    return any(needle in lower for needle in substrings)


def sleep_before_retry(attempt: int) -> None:
    """Sleep full-jitter exponential backoff before retry *attempt*.

    Delay is ``uniform(0, 2 ** attempt)`` seconds, so attempt 0 waits up
    to 1s, attempt 1 up to 2s, and so on — the schedule the gh wrapper
    relied on before this was extracted.
    """
    time.sleep(_rng.uniform(0, 2 ** attempt))
