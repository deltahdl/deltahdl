"""The gate over src/: no message there is reported under two subclauses."""

from pathlib import Path

from assert_subclause_citations import messages_citing_two_subclauses


def test_no_message_in_src_is_reported_under_two_subclauses(
    repo_root: Path,
) -> None:
    """One sentence sending a reader to two clauses fails here.

    Five messages did until #3119. `automatic variable in procedural
    continuous assignment` was reported under §6.21 and §13.3.2, and
    `drive_strength requires one strength0 keyword and one strength1 keyword`
    under §10.3.4 and §28.3.2, by sites enforcing two sentences apiece; the
    other three were one rule with one citation wrong. Nothing said so,
    because a unit test reads the report one source provoked and cannot see
    that another source reaches a different site emitting the same sentence.
    """
    assert not messages_citing_two_subclauses(repo_root / "src")
