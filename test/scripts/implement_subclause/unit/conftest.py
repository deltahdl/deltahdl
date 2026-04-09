"""Shared fixtures for implement_subclause unit tests."""

import json
from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def isc(module_loader):
    """Load the implement_subclause module."""
    return module_loader(
        "implement_subclause",
        SCRIPTS_DIR / "implement_subclause" / "__init__.py",
    )


def step2_envelope(verdict, *, evidence=None, rationale="rationale text"):
    """Build a Claude CLI envelope wrapping a Step 2 JSON payload."""
    payload = {
        "evidence": evidence if evidence is not None else [],
        "verdict": verdict,
        "rationale": rationale,
    }
    return json.dumps({"result": json.dumps(payload)})
