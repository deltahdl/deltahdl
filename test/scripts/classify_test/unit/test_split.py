"""Unit tests for _split helpers in classify_test."""

import importlib
from types import SimpleNamespace


def test_send_lrm_preamble_calls_claude(monkeypatch):
    """send_lrm_preamble calls run_claude_cli with the preamble prompt."""
    split_mod = importlib.import_module("classify_test._split")
    prompts = []

    def fake_run(_cmd, prompt, **_kw):
        prompts.append(prompt)
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    monkeypatch.setattr(split_mod, "run_claude_cli", fake_run)
    split_mod.send_lrm_preamble("6", "/lrm.pdf")
    assert "General or Overview" in prompts[0]
