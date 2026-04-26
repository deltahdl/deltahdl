"""Shared test fixtures and helpers for satisfaction-pipeline scripts."""

import json

from lib.python.satisfy import SATISFACTION_CONDITIONS, SATISFIED


def make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


def write_diagnostic(tmp_path, payload):
    """Write a diagnostic JSON file under *tmp_path* and return its path."""
    path = tmp_path / "diag.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def all_satisfied_payload():
    """Return a payload dict with every satisfaction condition satisfied."""
    return {condition: SATISFIED for condition in SATISFACTION_CONDITIONS}


def failing_payload(condition: str = "rule_coverage", *, failures=None):
    """Return a payload with one condition failing.

    Defaults to a single rule_coverage failure; the caller can pick a
    different condition or override the failure descriptions.
    """
    payload = all_satisfied_payload()
    payload[condition] = failures or [f"{condition} failed"]
    return payload
