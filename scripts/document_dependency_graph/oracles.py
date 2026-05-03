"""Atomic per-dependency oracles enriching the dependency graph.

Each oracle here issues one read-only Claude call with a single,
narrowly-scoped question. The dependency-list oracle remains in
``satisfy_subclause.oracles`` and is reused unchanged.
"""

import json
import re

from satisfy_subclause.oracles import run_oracle_call

from lib.python.lrm import build_lrm_read_instruction


_FENCED_STR_RE = re.compile(r"```(?:json)?\s*(.+?)\s*```", re.DOTALL)


def _strip_fences(text: str) -> str:
    match = _FENCED_STR_RE.search(text)
    return match.group(1) if match else text.strip()


def build_proof_sentence_prompt(
    subclause: str, dep: str, lrm: str,
) -> str:
    """Build the proof-sentence oracle prompt.

    The oracle returns the single sentence in §subclause that states
    the normative rule whose implementation needs §dep's machinery.
    """
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    return (
        f"You are the read-only proof-sentence oracle for the"
        f" §{subclause} → §{dep} dependency.\n\n"
        f"{read_ctx}\n\n"
        f"Quote the single sentence in §{subclause} that states the"
        f" normative rule whose implementation needs §{dep}'s"
        " machinery to already be in place. Quote verbatim — one"
        " sentence, no paraphrase.\n\n"
        "Read-only role: judge and report.\n\n"
        "Output the sentence as a single JSON string, e.g."
        ' "Module instantiation requires the elaborated definition'
        ' to already exist." Output nothing else.'
    )


def parse_proof_sentence(text: str) -> str:
    """Decode the proof-sentence oracle's response.

    Accepts a bare JSON string or a fenced ```json``` block. Rejects
    empty strings and non-string JSON values so a malformed response
    becomes a loud failure rather than a silent empty record.
    """
    body = _strip_fences(text)
    payload = json.loads(body)
    if not isinstance(payload, str):
        raise ValueError(
            f"Proof sentence must be a JSON string,"
            f" got {type(payload).__name__}",
        )
    if not payload:
        raise ValueError("Proof sentence is empty")
    return payload


def compute_proof_sentence(
    subclause: str, dep: str, lrm: str, *, model: str,
) -> str:
    """Run the proof-sentence oracle for one (§subclause, §dep) edge."""
    prompt = build_proof_sentence_prompt(subclause, dep, lrm)
    text = run_oracle_call(prompt, model=model)
    return parse_proof_sentence(text)


def build_prerequisites_prompt(
    subclause: str, dep: str, lrm: str,
) -> str:
    """Build the prerequisites oracle prompt.

    The oracle returns a description of what §subclause needs §dep
    to already provide before §subclause's normative rules can be
    implemented on top of it.
    """
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    return (
        f"You are the read-only prerequisites oracle for the"
        f" §{subclause} → §{dep} dependency.\n\n"
        f"{read_ctx}\n\n"
        f"Describe what §{subclause}'s implementation needs §{dep} to"
        " have already established — the machinery, behaviour, or"
        " state that must already be in place before §{subclause}'s"
        " normative rules can be implemented on top of it. One short"
        " phrase per prerequisite, joined as a single sentence.\n\n"
        "Read-only role: judge and report.\n\n"
        "Output a single JSON string, e.g. \"the elaborated module"
        ' definition and its parameter bindings". Output nothing'
        " else."
    )


def parse_prerequisites(text: str) -> str:
    """Decode the prerequisites oracle's response.

    Same shape as ``parse_proof_sentence`` — the oracle's contract
    is identical (one JSON string per call). Sharing the validator
    keeps the failure modes consistent across both oracles.
    """
    return parse_proof_sentence(text)


def compute_prerequisites(
    subclause: str, dep: str, lrm: str, *, model: str,
) -> str:
    """Run the prerequisites oracle for one (§subclause, §dep) edge."""
    prompt = build_prerequisites_prompt(subclause, dep, lrm)
    text = run_oracle_call(prompt, model=model)
    return parse_prerequisites(text)
