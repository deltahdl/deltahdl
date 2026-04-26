"""Shared fixtures and helpers for satisfy_subclause tests."""

import json
from unittest.mock import MagicMock

import pytest

from satisfy_subclause import streaming as _streaming
from satisfy_subclause.oracles import SATISFACTION_CONDITIONS, SATISFIED


@pytest.fixture()
def streaming():
    """Return the satisfy_subclause.streaming module."""
    return _streaming


def _build_satisfied_payload() -> dict:
    """Return a payload dict with every satisfaction condition satisfied."""
    return {condition: SATISFIED for condition in SATISFACTION_CONDITIONS}


@pytest.fixture()
def stub_completed():
    """Return a factory building stubbed ``CompletedProcess`` mocks."""

    def _make(stdout: str = "", returncode: int = 0, stderr: str = ""):
        completed = MagicMock()
        completed.returncode = returncode
        completed.stdout = stdout
        completed.stderr = stderr
        return completed

    return _make


@pytest.fixture()
def make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


@pytest.fixture()
def write_diagnostic(tmp_path):
    """Return a factory writing diagnostic JSON files under ``tmp_path``."""

    def _make(payload, *, name: str = "diag.json"):
        path = tmp_path / name
        path.write_text(json.dumps(payload), encoding="utf-8")
        return path

    return _make


@pytest.fixture()
def all_satisfied_payload():
    """Return a payload dict with every satisfaction condition satisfied."""
    return _build_satisfied_payload()


@pytest.fixture()
def failing_payload():
    """Return a factory producing payloads with one failing condition."""

    def _make(condition: str = "rule_coverage", *, failures=None):
        payload = _build_satisfied_payload()
        payload[condition] = failures or [f"{condition} failed"]
        return payload

    return _make
