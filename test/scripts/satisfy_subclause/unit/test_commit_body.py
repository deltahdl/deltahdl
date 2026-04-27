"""Unit tests for the satisfy_subclause commit-body generator.

Covers ``build_action_summary`` (the porcelain-derived fallback bullet
list), ``build_commit_prompt`` (the Claude prompt that asks for ``-
{Verb} `path` because reason.`` bullets), ``generate_commit_body`` (the
``--continue`` Claude call that produces them), and the
``COMMIT_BODY_DISALLOWED_TOOLS`` allow-list. The integration with
``commit_mutator_result`` lives in ``test_mutators.py``.
"""

from unittest.mock import patch

from satisfy_subclause.mutators import (
    COMMIT_BODY_DISALLOWED_TOOLS,
    build_action_summary,
    build_commit_prompt,
    generate_commit_body,
)


# --- build_action_summary ---------------------------------------------------


def test_build_action_summary_lists_added() -> None:
    """build_action_summary emits one '- Added path' bullet per added file."""
    summary = build_action_summary(["foo.cpp"], [], [])
    assert summary == "- Added foo.cpp"


def test_build_action_summary_lists_modified() -> None:
    """build_action_summary emits one '- Modified path' bullet per modified."""
    summary = build_action_summary([], ["bar.h"], [])
    assert summary == "- Modified bar.h"


def test_build_action_summary_lists_deleted() -> None:
    """build_action_summary emits one '- Deleted path' bullet per deleted."""
    summary = build_action_summary([], [], ["baz.py"])
    assert summary == "- Deleted baz.py"


def test_build_action_summary_sorts_each_section() -> None:
    """build_action_summary sorts each porcelain list alphabetically."""
    summary = build_action_summary(["b.cpp", "a.cpp"], [], [])
    assert summary == "- Added a.cpp\n- Added b.cpp"


def test_build_action_summary_empty_when_no_changes() -> None:
    """build_action_summary returns the empty string for empty input."""
    assert build_action_summary([], [], []) == ""


# --- build_commit_prompt ----------------------------------------------------


def test_build_commit_prompt_names_subclause() -> None:
    """The prompt names the subclause Claude just satisfied."""
    prompt = build_commit_prompt(["6.3"], ["foo.cpp"], [], [])
    assert "§6.3" in prompt


def test_build_commit_prompt_names_every_cycle_member() -> None:
    """Every cycle member appears in the prompt's scope label."""
    prompt = build_commit_prompt(
        ["33.4.1.5", "33.4.1.6"], ["foo.cpp"], [], [],
    )
    assert "§33.4.1.5" in prompt and "§33.4.1.6" in prompt


def test_build_commit_prompt_lists_added_paths() -> None:
    """Added porcelain paths appear in the prompt's file list."""
    prompt = build_commit_prompt(["6.3"], ["src/foo.cpp"], [], [])
    assert "Added: src/foo.cpp" in prompt


def test_build_commit_prompt_lists_modified_paths() -> None:
    """Modified porcelain paths appear in the prompt's file list."""
    prompt = build_commit_prompt(["6.3"], [], ["src/bar.h"], [])
    assert "Modified: src/bar.h" in prompt


def test_build_commit_prompt_lists_deleted_paths() -> None:
    """Deleted porcelain paths appear in the prompt's file list."""
    prompt = build_commit_prompt(["6.3"], [], [], ["src/baz.py"])
    assert "Deleted: src/baz.py" in prompt


def test_build_commit_prompt_sorts_added() -> None:
    """Added paths are listed in sorted order so the prompt is deterministic."""
    prompt = build_commit_prompt(
        ["6.3"], ["src/b.cpp", "src/a.cpp"], [], [],
    )
    assert prompt.index("Added: src/a.cpp") < prompt.index("Added: src/b.cpp")


def test_build_commit_prompt_demands_because_format() -> None:
    """The prompt requires the '- {Verb} `path` because reason.' shape."""
    prompt = build_commit_prompt(["6.3"], ["foo.cpp"], [], [])
    assert "because reason" in prompt


def test_build_commit_prompt_describes_move_collapse() -> None:
    """The prompt explains how to collapse an add+delete into a Moved bullet."""
    prompt = build_commit_prompt(["6.3"], ["foo.cpp"], [], [])
    assert "Moved" in prompt


def test_build_commit_prompt_demands_only_bullets() -> None:
    """The prompt forbids preamble/summary/trailing text."""
    prompt = build_commit_prompt(["6.3"], ["foo.cpp"], [], [])
    assert "Output ONLY the bullet list" in prompt


# --- generate_commit_body ---------------------------------------------------


def _patched_streaming_body():
    """Patch run_claude_streaming_with_retry; the stub returns a fixed body."""
    return patch(
        "satisfy_subclause.mutators.run_claude_streaming_with_retry",
        return_value="- Added `foo.cpp` because reasons.",
    )


def test_generate_commit_body_returns_runner_result() -> None:
    """generate_commit_body returns whatever the streaming runner returned."""
    with _patched_streaming_body():
        body = generate_commit_body(
            ["6.3"], ["foo.cpp"], [], [], model="opus",
        )
    assert body == "- Added `foo.cpp` because reasons."


def test_generate_commit_body_passes_model() -> None:
    """generate_commit_body forwards --model to the Claude CLI."""
    with _patched_streaming_body() as mock_run:
        generate_commit_body(["6.3"], ["foo.cpp"], [], [], model="haiku")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_generate_commit_body_uses_continue() -> None:
    """generate_commit_body resumes the eight-step session via --continue."""
    with _patched_streaming_body() as mock_run:
        generate_commit_body(["6.3"], ["foo.cpp"], [], [], model="opus")
    assert "--continue" in mock_run.call_args[0][0]


def test_generate_commit_body_uses_commit_disallowed_tools() -> None:
    """generate_commit_body forbids editing tools (Write/Edit/...)."""
    with _patched_streaming_body() as mock_run:
        generate_commit_body(["6.3"], ["foo.cpp"], [], [], model="opus")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--disallowedTools") + 1] == COMMIT_BODY_DISALLOWED_TOOLS


def test_generate_commit_body_passes_prompt_with_paths() -> None:
    """The prompt fed to the runner lists the porcelain paths."""
    with _patched_streaming_body() as mock_run:
        generate_commit_body(
            ["6.3"], ["src/foo.cpp"], [], [], model="opus",
        )
    assert "src/foo.cpp" in mock_run.call_args[0][1]


def test_generate_commit_body_uses_commit_body_role() -> None:
    """The retry helper sees the 'Commit body' role for content-filter logs."""
    with _patched_streaming_body() as mock_run:
        generate_commit_body(["6.3"], ["foo.cpp"], [], [], model="opus")
    assert mock_run.call_args[1]["role"] == "Commit body"


def test_generate_commit_body_retry_cmd_uses_continue() -> None:
    """The retry_cmd handed to the helper also keeps --continue."""
    with _patched_streaming_body() as mock_run:
        generate_commit_body(["6.3"], ["foo.cpp"], [], [], model="opus")
    assert "--continue" in mock_run.call_args[1]["retry_cmd"]


# --- COMMIT_BODY_DISALLOWED_TOOLS -------------------------------------------


def test_commit_body_disallowed_tools_blocks_write() -> None:
    """Commit-body generation must not write files."""
    assert "Write" in COMMIT_BODY_DISALLOWED_TOOLS


def test_commit_body_disallowed_tools_blocks_edit() -> None:
    """Commit-body generation must not edit files."""
    assert "Edit" in COMMIT_BODY_DISALLOWED_TOOLS


def test_commit_body_disallowed_tools_blocks_git() -> None:
    """Commit-body generation must not run git directly."""
    assert "Bash(git *)" in COMMIT_BODY_DISALLOWED_TOOLS
