"""Shared utilities for LRM clause implementation automation."""

import glob
import os
import re
import subprocess
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Supplementary file directories (Figures and Tables)
# ---------------------------------------------------------------------------

_GDRIVE = Path(
    "/Users/jdrowne/Library/CloudStorage/"
    "GoogleDrive-jdrowne@10ulabs.com/Shared drives/"
    "10U Labs Shared Drive/Standards/SystemVerilog"
)
FIGURES_DIR = _GDRIVE / "Figures"
TABLES_DIR = _GDRIVE / "Tables"


# ---------------------------------------------------------------------------
# LRM title extraction
# ---------------------------------------------------------------------------

def load_lrm_titles(lrm_path: Path) -> dict[str, str]:
    """Build clause -> title map from an LRM text file.

    Handles three formats:
    - Subclauses: "4.1 General" or "A.8.1 Concatenations"
    - Top-level numeric: "4. Scheduling semantics"
    - Annex headers (multi-line): "Annex B\\n(normative)\\n\\nKeywords"
    """
    if not lrm_path.exists():
        return {}

    titles = {}
    lines = lrm_path.read_text(encoding="utf-8").splitlines()

    for i, line in enumerate(lines):
        # Subclauses: "4.1 General", "A.8.1 Concatenations"
        m = re.match(r"^(\d+(?:\.\d+)+)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
            continue
        m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
            continue

        # Top-level numeric: "4. Scheduling semantics"
        m = re.match(r"^(\d+)\.\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
            continue

        # Annex headers (multi-line):
        #   Annex B
        #   (normative)
        #
        #   Keywords
        m = re.match(r"^Annex\s+([A-Z])$", line)
        if m:
            letter = m.group(1)
            normative = ""
            title = ""
            # Look ahead for (normative)/(informative) and title
            for j in range(i + 1, min(i + 6, len(lines))):
                nxt = lines[j].strip()
                if not nxt:
                    continue
                nm = re.match(r"^\((normative|informative)\)$", nxt)
                if nm:
                    normative = f"({nm.group(1)})"
                    continue
                # First non-empty, non-normative line is the title
                title = nxt
                break
            if normative and title:
                titles[letter] = f"{normative} {title}"
            elif title:
                titles[letter] = title

    return titles


# ---------------------------------------------------------------------------
# Hierarchy computation
# ---------------------------------------------------------------------------

def build_hierarchy(clause: str) -> dict:
    """Derive template variables from a clause string.

    Returns a dict with keys:
    - is_annex, subclause (always present)
    - Numeric: clause_number, principle (depth >= 3), ancestors
    - Annex: collection, letter, principles (depth >= 2), ancestors
    """
    parts = clause.split(".")
    is_annex = parts[0][0].isalpha() and parts[0][0].isupper()
    depth = len(parts)

    result = {"is_annex": is_annex, "subclause": clause}

    if is_annex:
        letter = parts[0]
        result["collection"] = f"Annex {letter}"
        result["letter"] = letter
        if depth >= 2:
            result["principles"] = f"{letter}.{parts[1]}"
        # Ancestors: intermediate levels between principles (V.W) and
        # subclause. For depth 3 (A.8.1), no ancestors. For depth 4
        # (A.7.5.3), ancestors = [A.7.5].
        ancestors = []
        for k in range(3, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors
    else:
        result["clause_number"] = parts[0]
        if depth >= 3:
            result["principle"] = f"{parts[0]}.1"
        # Ancestors: intermediate levels between principle (V.1) and
        # subclause. For depth 3 (6.24.1), ancestors = [6.24]. For
        # depth 4 (4.4.3.1), ancestors = [4.4, 4.4.3].
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors

    return result


# ---------------------------------------------------------------------------
# Supplementary files (Figures / Tables)
# ---------------------------------------------------------------------------

def find_supplementary_files(clause: str) -> list[tuple[str, Path]]:
    """Find converted Figure/Table files for the clause's top-level component.

    Returns (human_label, path) pairs for files that exist on disk.
    """
    top = clause.split(".")[0]
    results = []

    if FIGURES_DIR.is_dir():
        for path in sorted(FIGURES_DIR.glob(f"Figure_{top}_*.gv")):
            # Figure_4_1.gv -> "Figure 4-1"
            stem = path.stem  # "Figure_4_1"
            label = stem.replace("_", " ", 1).replace("_", "-")
            results.append((label, path))

    if TABLES_DIR.is_dir():
        for path in sorted(TABLES_DIR.glob(f"TABLE_{top}_*.md")):
            # TABLE_B_1.md -> "Table B-1"
            stem = path.stem  # "TABLE_B_1"
            raw = stem[len("TABLE_"):]  # "B_1"
            label = f"Table {raw.replace('_', '-')}"
            results.append((label, path))

    return results


def build_supplementary_lines(clause: str) -> str:
    """Build prompt lines acknowledging available Figures/Tables."""
    files = find_supplementary_files(clause)
    if not files:
        return ""
    lines = []
    for label, path in files:
        if path.suffix == ".gv":
            fmt = "a DOT GraphViz"
        elif path.suffix == ".md":
            fmt = "a Markdown file"
        else:
            fmt = "a file"
        lines.append(
            f"- Acknowledge that you know {label} is available"
            f" at {path} as {fmt}"
        )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Claude CLI invocation
# ---------------------------------------------------------------------------

def invoke_claude(prompt: str, *, model: str = "sonnet") -> None:
    """Launch Claude CLI in print mode with the implementation prompt.

    Streams stdout/stderr to the terminal in real time.
    """
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    cmd = [
        "claude", "-p",
        "--model", model,
        "--dangerously-skip-permissions",
    ]

    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=sys.stdout,
        stderr=sys.stderr,
        text=True,
        env=env,
    )
    proc.stdin.write(prompt)
    proc.stdin.close()
    proc.wait()

    if proc.returncode != 0:
        print(
            f"\nERROR: Claude exited with code {proc.returncode}",
            file=sys.stderr,
        )
        sys.exit(1)


# ---------------------------------------------------------------------------
# Post-implementation: split_tests.py
# ---------------------------------------------------------------------------

def run_split_tests(lrm_path: Path) -> None:
    """Run split_tests.py on any new/modified test files."""
    repo_root = Path(__file__).resolve().parent.parent.parent
    script = repo_root / "scripts" / "split_tests.py"
    test_dir = repo_root / "test" / "src" / "unit"
    arch = repo_root / "docs" / "ARCHITECTURE.md"

    result = subprocess.run(
        ["git", "diff", "--name-only", "HEAD"],
        capture_output=True, text=True, check=False,
    )
    changed = result.stdout.strip().splitlines()
    test_files = [
        f for f in changed
        if f.startswith("test/src/unit/test_") and f.endswith(".cpp")
    ]

    if not test_files:
        print("No new/modified test files to split.")
        return

    for tf in test_files:
        full_path = repo_root / tf
        if not full_path.exists():
            continue
        print(f"Running split_tests.py on {tf}...")
        subprocess.run(
            [
                sys.executable, str(script),
                "--file", str(full_path),
                "--output-dir", str(test_dir),
                "--lrm", str(lrm_path),
                "--arch", str(arch),
            ],
            check=False,
        )
