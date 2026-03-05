"""Shared test fixtures."""

import sys


def capture_help_output(parse_func, monkeypatch, capsys):
    """Call *parse_func* with ``--help`` and return captured stdout."""
    monkeypatch.setattr(sys, "argv", ["prog", "--help"])
    try:
        parse_func()
    except SystemExit:
        pass
    return capsys.readouterr().out
