"""File-generation helpers for classify_test."""

import re

from ._split import _render_tests, strip_lrm_quotes


def _preamble_name(item):
    """Extract the identifier (struct/class/enum/function name) from a item."""
    for line in item.lines:
        stripped = line.strip()
        if stripped.startswith("//"):
            continue
        m = re.match(
            r"(?:struct|class|enum)\s+(\w+)\s*\{", stripped,
        )
        if m:
            return m.group(1)
        m = re.match(
            r"(?:[\w*&:]+\s+)*(\w+)\s*\(", stripped,
        )
        if m:
            return m.group(1)
        return None
    return None


def _filter_preamble(items, tests):
    """Return only preamble items referenced (directly or transitively)."""
    names = {}
    for item in items:
        name = _preamble_name(item)
        if name:
            names[name] = item
    text_pool = "\n".join(
        line for t in tests for line in t.lines
    )
    kept = set()
    for name, item in names.items():
        if re.search(r'\b' + re.escape(name) + r'\b', text_pool):
            kept.add(id(item))
    changed = True
    while changed:
        changed = False
        for name, item in names.items():
            if id(item) in kept:
                continue
            for _, other in names.items():
                if id(other) in kept and re.search(
                    r'\b' + re.escape(name) + r'\b',
                    "\n".join(other.lines),
                ):
                    kept.add(id(item))
                    changed = True
                    break
    return [
        item for item in items
        if _preamble_name(item) is None or id(item) in kept
    ]


def generate_file(clause, title, parsed, tests):
    """Generate the content of a split test file."""
    out = []
    if clause == "non-lrm":
        out.append("// Non-LRM tests")
    elif re.match(r"^[A-Z]\.", clause):
        hdr = f"// Annex {clause}: {title}" if title else f"// Annex {clause}"
        out.append(hdr)
    else:
        hdr = f"// §{clause}: {title}" if title else f"// §{clause}"
        out.append(hdr)
    out.append("")
    for inc in parsed.includes:
        out.append(inc)
    out.append("")
    if parsed.using_line:
        out.append(parsed.using_line)
        out.append("")
    all_preamble = _filter_preamble(
        parsed.global_preamble + parsed.section_preamble, tests,
    )
    for item in all_preamble:
        for line in item.lines:
            cleaned = strip_lrm_quotes(line)
            if cleaned or cleaned == "":  # pragma: no branch
                out.append(cleaned)
        out.append("")
    out.append("namespace {")
    out.append("")
    out.extend(_render_tests(tests))
    out.append("}  // namespace")
    out.append("")
    return "\n".join(out)
