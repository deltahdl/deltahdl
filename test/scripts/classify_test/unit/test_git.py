"""Unit tests for git integration functions in classify_test."""

from types import SimpleNamespace


# ---- build_commit_message --------------------------------------------------


def test_build_commit_message_title_has_test_name(ct_git):
    """Title line contains the test name."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("FooBar", "6.1", "rationale text")
    assert "Classify FooBar" in msg.splitlines()[0]


def test_build_commit_message_title_has_clause(ct_git):
    """Title line contains the formatted clause with section sign."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "§6.1" in msg.splitlines()[0]


def test_build_commit_message_title_has_skip_ci(ct_git):
    """Title line contains [skip ci]."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "[skip ci]" in msg.splitlines()[0]


def test_build_commit_message_title_has_arrow(ct_git):
    """Title line uses arrow separator."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "→" in msg.splitlines()[0]


def test_build_commit_message_title_format(ct_git):
    """Title line matches exact format."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("MyTest", "9.2.1", "r")
    assert msg.splitlines()[0] == "Classify MyTest → §9.2.1 [skip ci]"


def test_build_commit_message_non_lrm_clause(ct_git):
    """Non-LRM clause formats as 'Non-LRM TOPIC'."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "non-lrm:aig", "r")
    assert "Non-LRM AIG" in msg.splitlines()[0]


def test_build_commit_message_non_lrm_underscore(ct_git):
    """Non-LRM clause with underscore converts to space."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "non-lrm:aig_opt", "r")
    assert "Non-LRM AIG OPT" in msg.splitlines()[0]


def test_build_commit_message_has_co_authored_by(ct_git):
    """Message contains Co-Authored-By trailer."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>" in msg


def test_build_commit_message_rationale_in_body(ct_git):
    """Rationale text appears in message body."""
    build_commit_message = ct_git.build_commit_message
    rationale = "This test exercises the UDP initial statement construct."
    msg = build_commit_message("T", "6.1", rationale)
    assert rationale in msg


def test_build_commit_message_exhaustive_rationale(ct_git):
    """Full multi-sentence rationale is preserved, not truncated."""
    build_commit_message = ct_git.build_commit_message
    rationale = (
        "This test exercises the UDP initial statement construct "
        "defined in §29.7. The grammar production "
        "udp_initial_statement sets the starting value of a "
        "sequential UDP output register."
    )
    msg = build_commit_message("T", "29.7", rationale)
    assert rationale in msg


def test_build_commit_message_blank_line_after_title(ct_git):
    """Blank line separates title from body."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "rationale")
    lines = msg.splitlines()
    assert lines[1] == ""


def test_build_commit_message_blank_line_before_trailer(ct_git):
    """Blank line separates body from Co-Authored-By trailer."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "rationale")
    lines = msg.splitlines()
    trailer_idx = next(
        i for i, l in enumerate(lines) if "Co-Authored-By" in l
    )
    assert lines[trailer_idx - 1] == ""


def test_build_commit_message_annex_clause(ct_git):
    """Annex clause formats with section sign."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "A.6.3", "r")
    assert "§A.6.3" in msg.splitlines()[0]


# ---- commit_classification ---------------------------------------------------


def _stub_commit_push(monkeypatch, ct_git):
    """Stub commit_and_push to capture arguments."""
    captured = {}

    def fake(changed, deleted, message):
        captured["changed"] = list(changed)
        captured["deleted"] = list(deleted)
        captured["message"] = message

    monkeypatch.setattr(ct_git, "commit_and_push", fake)
    return captured


def _make_ctx(tmp_path, **overrides):
    """Build a commit_classification context dict."""
    defaults = {
        "filepath": tmp_path / "test_input.cpp",
        "target": [SimpleNamespace(
            test_name="T", clause="6.1", rationale="r",
        )],
        "new_names": [],
        "to_merge": [],
        "test_dir": tmp_path,
        "cmake_path": tmp_path / "CMakeLists.txt",
    }
    defaults.update(overrides)
    return defaults


def test_commit_classification_includes_new_files(monkeypatch, tmp_path, ct_git):
    """Changed files include newly created output files."""
    commit_classification = ct_git.commit_classification
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, new_names=["test_parser_clause_06_01"])
    commit_classification(ctx)
    assert tmp_path / "test_parser_clause_06_01.cpp" in captured["changed"]


def test_commit_classification_includes_merged(monkeypatch, tmp_path, ct_git):
    """Changed files include merge targets."""
    commit_classification = ct_git.commit_classification
    merge_path = tmp_path / "test_parser_clause_06_01.cpp"
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, to_merge=[(merge_path, None)])
    commit_classification(ctx)
    assert merge_path in captured["changed"]


def test_commit_classification_includes_cmake(monkeypatch, tmp_path, ct_git):
    """Changed files include CMakeLists.txt."""
    commit_classification = ct_git.commit_classification
    cmake = tmp_path / "CMakeLists.txt"
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, cmake_path=cmake)
    commit_classification(ctx)
    assert cmake in captured["changed"]


def test_commit_classification_existing_source_in_changed(
    monkeypatch, tmp_path, ct_git,
):
    """Source file that still exists goes into changed list."""
    commit_classification = ct_git.commit_classification
    src = tmp_path / "test_input.cpp"
    src.touch()
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, filepath=src)
    commit_classification(ctx)
    assert src in captured["changed"]


def test_commit_classification_deleted_source_in_deleted(
    monkeypatch, tmp_path, ct_git,
):
    """Source file that was removed goes into deleted list."""
    commit_classification = ct_git.commit_classification
    src = tmp_path / "test_input.cpp"
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, filepath=src)
    commit_classification(ctx)
    assert src in captured["deleted"]


def test_commit_classification_message_has_test_name(monkeypatch, tmp_path, ct_git):
    """Commit message includes the test name."""
    commit_classification = ct_git.commit_classification
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, target=[SimpleNamespace(
        test_name="FooBar", clause="6.1", rationale="r",
    )])
    commit_classification(ctx)
    assert "FooBar" in captured["message"]
