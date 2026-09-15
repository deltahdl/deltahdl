import random
import time

DEFAULT_MAX_ATTEMPTS = 10

_rng = random.Random()


def contains_transient_marker(text: str, substrings: tuple[str, ...]) -> bool:
    lower = text.lower()
    return any(needle in lower for needle in substrings)


def sleep_before_retry(attempt: int) -> None:
    time.sleep(_rng.uniform(0, 2 ** attempt))
