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
    try:
        parse_dependencies(payload, toc=_NET_TOC)
    except UnknownSubclauseRejection as exc:
        return exc.identifiers
    return []


def test_absent_identifiers_are_collected_in_payload_order() -> None:
    assert _absent('["23.3.7", "23.9.1"]') == ["23.3.7", "23.9.1"]


def test_present_identifier_is_left_out_of_the_rejection() -> None:
    assert _absent('["23.3.3.7", "23.3.7"]') == ["23.3.7"]


def test_absent_section_is_reported_before_an_aggregate_one() -> None:
    with pytest.raises(UnknownSubclauseRejection):
        parse_dependencies('["23", "23.3.7"]', toc=_NET_TOC)


def test_malformed_identifier_still_short_circuits() -> None:
    captured: ValueError | None = None
    try:
        parse_dependencies('["not-a-clause", "23.3.7"]', toc=_NET_TOC)
    except ValueError as exc:
        captured = exc
    assert not isinstance(captured, UnknownSubclauseRejection)


def test_rejection_message_quotes_every_absent_identifier() -> None:
    captured = ""
    try:
        parse_dependencies('["23.3.7", "23.9.1"]', toc=_NET_TOC)
    except UnknownSubclauseRejection as exc:
        captured = str(exc)
    missing = [i for i in ("'23.3.7'", "'23.9.1'") if i not in captured]
    assert not missing


def test_empty_table_of_contents_accepts_an_identifier_it_lacks() -> None:
    assert validate_dependencies(["23.3.7"], toc={}) == ["23.3.7"]


def test_empty_table_of_contents_announces_the_skipped_check(
    capsys: pytest.CaptureFixture[str],
) -> None:
    validate_dependencies(["23.3.7"], toc={})
    assert "were not checked" in capsys.readouterr().err


def test_unknown_subclause_rejection_is_a_value_error() -> None:
    assert issubclass(UnknownSubclauseRejection, ValueError)


def test_unknown_subclause_rejection_stores_identifiers() -> None:
    rejection = UnknownSubclauseRejection(["23.3.7"], "no section numbered")
    assert rejection.identifiers == ["23.3.7"]


def test_unknown_subclause_rejection_str_returns_message() -> None:
    rejection = UnknownSubclauseRejection(["23.3.7"], "the message")
    assert str(rejection) == "the message"


def test_unknown_retry_prompt_embeds_the_reason() -> None:
    prompt = build_unknown_retry_prompt("no section numbered '23.3.7'", ["23.3.7"])
    assert "no section numbered '23.3.7'" in prompt


def test_unknown_retry_prompt_quotes_every_identifier() -> None:
    prompt = build_unknown_retry_prompt("reason", ["23.3.7", "23.9.1"])
    missing = [i for i in ("'23.3.7'", "'23.9.1'") if i not in prompt]
    assert not missing


def test_unknown_retry_prompt_warns_about_a_neighbouring_number() -> None:
    prompt = build_unknown_retry_prompt("reason", ["23.3.7"])
    assert "different subject" in prompt


def _retry_after_absent(corrected: str) -> tuple[Any, SubclauseDependencies]:
    with patched_oracle_sequence(
        '["23.3.7"]', corrected,
    ) as mock_run, patched_toc(_NET_TOC):
        deps = compute_subclause_dependencies("23.4", "lrm.pdf", model="opus")
    return mock_run, deps


def test_absent_section_costs_one_retry() -> None:
    mock_run, _deps = _retry_after_absent('["23.3.3.7"]')
    assert mock_run.call_count == 2


def test_absent_section_retry_uses_the_absent_section_prompt() -> None:
    mock_run, _deps = _retry_after_absent('["23.3.3.7"]')
    assert "different subject" in mock_run.call_args_list[1].args[0]


def test_absent_section_retry_returns_the_corrected_answer() -> None:
    _mock_run, deps = _retry_after_absent('["23.3.3.7"]')
    assert deps == ["23.3.3.7"]
