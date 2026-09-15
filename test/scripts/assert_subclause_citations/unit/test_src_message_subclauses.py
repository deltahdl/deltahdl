from pathlib import Path

from assert_subclause_citations import messages_citing_two_subclauses


def test_no_message_in_src_is_reported_under_two_subclauses(
    repo_root: Path,
) -> None:
    assert not messages_citing_two_subclauses(repo_root / "src")
