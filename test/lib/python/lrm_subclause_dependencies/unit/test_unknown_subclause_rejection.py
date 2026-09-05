"""Unit tests for rejecting dependency identifiers that name no section.

An identifier can satisfy the dotted-decimal grammar, name no aggregate
top-level entry, and still name nothing at all: IEEE 1800-2023 has no
§23.3.7, though it does have §23.3.3.7 carrying the subject a reader
would look for under that number. These tests cover the check that
catches such an identifier, the rejection it raises, and the corrective
turn fed back to the oracle.
"""

from typing import Any

import pytest

from lib.python.lrm_subclause_dependencies import (
    SubclauseDependencies,
    UnknownSubclauseRejection,
    build_unknown_retry_prompt,
    compute_subclause_dependencies,
    parse_dependencies,
    validate_dependencies,
)
from lib.python.test_fixtures.lrm_subclause_dependencies import (
    patched_oracle_sequence,
    patched_toc,
)


# §23.3 runs out at §23.3.3, whose own §23.3.3.7 holds the dominating-net
# rules a reader might reach for under a §23.3.7 that never existed. §23
# is an aggregate here, so a payload can name an absent section and an
# aggregate one at once.
_NET_TOC: dict[str, tuple[int, int]] = {
    "23": (700, 760),
    "23.3": (712, 720),
    "23.3.1": (712, 714),
    "23.3.2": (715, 716),
    "23.3.3": (717, 720),
    "23.3.3.7": (719, 720),
    "23.4": (721, 730),
}


def _absent(payload: str) -> list[str]:
    """Return the identifiers a rejection of *payload* reported as absent."""
    try:
        parse_dependencies(payload, toc=_NET_TOC)
    except UnknownSubclauseRejection as exc:
        return exc.identifiers
    return []


# --- validate_dependencies: the existence check -----------------------------


def test_absent_identifiers_are_collected_in_payload_order() -> None:
    """Two absent section numbers are reported together, in the payload's order.

    One corrective turn can then present both, rather than the retry
    budget being spent a section at a time.
    """
    assert _absent('["23.3.7", "23.9.1"]') == ["23.3.7", "23.9.1"]


def test_present_identifier_is_left_out_of_the_rejection() -> None:
    """A section the table of contents holds is not reported as absent."""
    assert _absent('["23.3.3.7", "23.3.7"]') == ["23.3.7"]


def test_absent_section_is_reported_before_an_aggregate_one() -> None:
    """Whether a section exists is settled before what kind of section it is.

    An aggregate rejection describes an entry the table of contents
    holds. There is nothing to describe about an entry it does not
    hold, so the absent ones are raised first.
    """
    with pytest.raises(UnknownSubclauseRejection):
        parse_dependencies('["23", "23.3.7"]', toc=_NET_TOC)


def test_malformed_identifier_still_short_circuits() -> None:
    """A malformed entry raises the plain shape error beside an absent section.

    A payload whose shape is wrong has to be replaced whole, so it never
    reaches the point where absent sections are collected.
    """
    captured: ValueError | None = None
    try:
        parse_dependencies('["not-a-clause", "23.3.7"]', toc=_NET_TOC)
    except ValueError as exc:
        captured = exc
    assert not isinstance(captured, UnknownSubclauseRejection)


def test_rejection_message_quotes_every_absent_identifier() -> None:
    """The message the corrective prompt embeds names each offender."""
    captured = ""
    try:
        parse_dependencies('["23.3.7", "23.9.1"]', toc=_NET_TOC)
    except UnknownSubclauseRejection as exc:
        captured = str(exc)
    missing = [i for i in ("'23.3.7'", "'23.9.1'") if i not in captured]
    assert not missing


# --- validate_dependencies: an empty table of contents ----------------------


def test_empty_table_of_contents_accepts_an_identifier_it_lacks() -> None:
    """An unreadable outline says nothing about which sections exist.

    ``load_toc`` returns an empty table for a PDF it cannot read.
    Judging identifiers against that table would turn down every one of
    them, so the check stands down and the identifier survives.
    """
    assert validate_dependencies(["23.3.7"], toc={}) == ["23.3.7"]


def test_empty_table_of_contents_announces_the_skipped_check(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A check that did not run says so, rather than reading as one that passed."""
    validate_dependencies(["23.3.7"], toc={})
    assert "were not checked" in capsys.readouterr().err


# --- UnknownSubclauseRejection ----------------------------------------------


def test_unknown_subclause_rejection_is_a_value_error() -> None:
    """The parse-retry loop catches ValueError, so the rejection has to be one."""
    assert issubclass(UnknownSubclauseRejection, ValueError)


def test_unknown_subclause_rejection_stores_identifiers() -> None:
    """The corrective prompt reads the rejected identifiers off the exception."""
    rejection = UnknownSubclauseRejection(["23.3.7"], "no section numbered")
    assert rejection.identifiers == ["23.3.7"]


def test_unknown_subclause_rejection_str_returns_message() -> None:
    """str() returns the message the retry loop logs and embeds."""
    rejection = UnknownSubclauseRejection(["23.3.7"], "the message")
    assert str(rejection) == "the message"


# --- build_unknown_retry_prompt ---------------------------------------------


def test_unknown_retry_prompt_embeds_the_reason() -> None:
    """The corrective prompt repeats why the previous array was turned down."""
    prompt = build_unknown_retry_prompt("no section numbered '23.3.7'", ["23.3.7"])
    assert "no section numbered '23.3.7'" in prompt


def test_unknown_retry_prompt_quotes_every_identifier() -> None:
    """Naming only the first offender would spend a retry on each of the rest."""
    prompt = build_unknown_retry_prompt("reason", ["23.3.7", "23.9.1"])
    missing = [i for i in ("'23.3.7'", "'23.9.1'") if i not in prompt]
    assert not missing


def test_unknown_retry_prompt_warns_about_a_neighbouring_number() -> None:
    """A number close to the rejected one can exist and carry a different subject.

    That is the failure the check exists to stop: §23.3.7 read as the
    §23.3.3.7 next to it, whose files another pass owns.
    """
    prompt = build_unknown_retry_prompt("reason", ["23.3.7"])
    assert "different subject" in prompt


# --- compute_subclause_dependencies: the corrective turn --------------------


def _retry_after_absent(corrected: str) -> tuple[Any, SubclauseDependencies]:
    """Answer §23.3.7 then *corrected*; return the oracle mock and the result."""
    with patched_oracle_sequence(
        '["23.3.7"]', corrected,
    ) as mock_run, patched_toc(_NET_TOC):
        deps = compute_subclause_dependencies("23.4", "lrm.pdf", model="opus")
    return mock_run, deps


def test_absent_section_costs_one_retry() -> None:
    """An answer naming a section the table of contents lacks is asked again."""
    mock_run, _deps = _retry_after_absent('["23.3.3.7"]')
    assert mock_run.call_count == 2


def test_absent_section_retry_uses_the_absent_section_prompt() -> None:
    """The corrective turn is the one written for a section that does not exist.

    An aggregate's turn enumerates its direct numbered children, and a
    section the table of contents lacks has none to enumerate.
    """
    mock_run, _deps = _retry_after_absent('["23.3.3.7"]')
    assert "different subject" in mock_run.call_args_list[1].args[0]


def test_absent_section_retry_returns_the_corrected_answer() -> None:
    """The number the section actually carries reaches the caller."""
    _mock_run, deps = _retry_after_absent('["23.3.3.7"]')
    assert deps == ["23.3.3.7"]
