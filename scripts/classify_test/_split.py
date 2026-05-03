"""File-splitting helpers for classify_test."""

import glob
import re
from pathlib import Path
from typing import Any


def strip_lrm_quotes(line: str) -> str:
    """Remove LRM prose quotes from comments."""
    if re.search(r'//.*"[A-Z].*"', line):
        m = re.match(r'(//\s*§[\d.]+:?\s*)(".*")', line)
        if m:
            return m.group(1).rstrip()
        return ""
    return line


def _count_file_lines(path: Path) -> int:
    """Return the number of lines in a file, or 0 if it does not exist."""
    if not path.exists():
        return 0
    return len(path.read_text(encoding="utf-8").splitlines())


def _next_suffix_file(target_base: str, test_dir: Path) -> str:
    """Return the next available single-letter suffix (a, b, c, ...)."""
    variants = sorted(
        glob.glob(str(test_dir / f"{target_base}_[a-z].cpp")),
    )
    if not variants:
        return "a"
    last = Path(variants[-1]).stem[-1]
    return chr(ord(last) + 1)


def _rename_base_to_suffix(target_base: str, test_dir: Path) -> Path:
    """Rename base file to next available suffix; return new path."""
    suffix = _next_suffix_file(target_base, test_dir)
    base = test_dir / f"{target_base}.cpp"
    dest = test_dir / f"{target_base}_{suffix}.cpp"
    base.rename(dest)
    return dest


def _test_line_count(test: Any) -> int:
    """Return the number of lines a test block will occupy."""
    count = len(test.lines) + 1  # +1 for trailing blank line
    for line in test.preceding_comments:
        if strip_lrm_quotes(line):
            count += 1
    return count


def _render_tests(tests: list[Any]) -> list[str]:
    """Render test blocks to a flat list of lines."""
    out: list[str] = []
    for t in tests:
        for line in t.preceding_comments:
            cleaned = strip_lrm_quotes(line)
            if cleaned:
                out.append(cleaned)
        for line in t.lines:
            out.append(strip_lrm_quotes(line))
        out.append("")
    return out


def _split_tests(
    tests: list[Any], file_len: int, max_lines: int | None,
) -> tuple[list[Any], list[Any]]:
    """Partition tests into (fit, overflow) given current file length."""
    fit: list[Any] = []
    overflow: list[Any] = []
    current = file_len
    for t in tests:
        n = _test_line_count(t)
        if max_lines and current + n > max_lines:
            overflow.append(t)
        else:
            fit.append(t)
            current += n
    return fit, overflow


def _flush_overflow(
    overflow: list[Any],
    base: str,
    test_dir: Path,
    source_path: Path,
    max_lines: int | None,
) -> list[str]:
    """Write overflow tests to new suffix file(s); return new names."""
    new_names: list[str] = []
    batch: list[Any] = []
    batch_lines = 0
    for t in overflow:
        n = _test_line_count(t)
        if batch and max_lines and batch_lines + n > max_lines:
            sfx = _next_suffix_file(base, test_dir)
            out = f"{base}_{sfx}"
            _write_overflow_file(test_dir / f"{out}.cpp", source_path, batch)
            new_names.append(out)
            batch, batch_lines = [], 0
        batch.append(t)
        batch_lines += n
    if batch:
        sfx = _next_suffix_file(base, test_dir)
        out = f"{base}_{sfx}"
        _write_overflow_file(test_dir / f"{out}.cpp", source_path, batch)
        new_names.append(out)
    return new_names


def _dedup_preamble(global_preamble: list[Any], text: str) -> list[str]:
    """Return preamble lines not already present in text."""
    out: list[str] = []
    for item in global_preamble:
        first_code = next(
            (ln for ln in item.lines if not ln.strip().startswith("//")),
            item.lines[0],
        )
        if first_code.strip() not in text:
            out.extend(item.lines)
            out.append("")
    return out


def _find_namespace_close(lines: list[str]) -> int:
    """Return index of }  // namespace line, or len(lines)."""
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() in ("}  // namespace", "} // namespace"):
            return i
    return len(lines)


def append_tests_to_file(
    filepath: Path,
    global_preamble: list[Any],
    tests: list[Any],
    max_lines: int | None = None,
    section_preamble: list[Any] | None = None,
) -> list[str]:
    """Append tests to an existing file before closing }  // namespace.

    Returns a list of new filenames created by splitting (empty if no
    splitting occurred).
    """
    text = filepath.read_text(encoding="utf-8")
    lines = text.splitlines()
    insert_idx = _find_namespace_close(lines)
    all_preamble = list(global_preamble) + list(section_preamble or [])
    new_lines = _dedup_preamble(all_preamble, text)

    fit, overflow = _split_tests(
        tests, len(lines) + len(new_lines), max_lines,
    )
    new_lines.extend(_render_tests(fit))
    lines[insert_idx:insert_idx] = new_lines
    filepath.write_text("\n".join(lines) + "\n", encoding="utf-8")

    if not max_lines or not overflow:
        return []

    new_names: list[str] = []
    base = re.sub(r"_[a-z]$", "", filepath.stem)
    if filepath.stem == base:
        renamed = _rename_base_to_suffix(base, filepath.parent)
        new_names.append(renamed.stem)
        filepath = renamed
    new_names.extend(_flush_overflow(
        overflow, base, filepath.parent, filepath, max_lines,
    ))
    return new_names


def _write_overflow_file(
    outpath: Path, source_path: Path, tests: list[Any],
) -> None:
    """Write overflow tests to a new file, copying the header from source."""
    source_text = source_path.read_text(encoding="utf-8")
    source_lines = source_text.splitlines()
    # Copy everything up to and including "namespace {" + blank line.
    header: list[str] = []
    for line in source_lines:
        header.append(line)
        if line.strip() == "namespace {":
            header.append("")
            break
    for t in tests:
        for line in t.preceding_comments:
            cleaned = strip_lrm_quotes(line)
            if cleaned:
                header.append(cleaned)
        for line in t.lines:
            header.append(strip_lrm_quotes(line))
        header.append("")
    header.append("}  // namespace")
    header.append("")
    outpath.write_text("\n".join(header), encoding="utf-8")


def _batch_tests(
    tests: list[Any], header_lines: int, max_lines: int,
) -> list[list[Any]]:
    """Split tests into batches that each fit within max_lines."""
    batches: list[list[Any]] = []
    current_batch: list[Any] = []
    current_len = header_lines
    for t in tests:
        n = _test_line_count(t)
        if current_batch and current_len + n > max_lines:
            batches.append(current_batch)
            current_batch = []
            current_len = header_lines
        current_batch.append(t)
        current_len += n
    if current_batch:
        batches.append(current_batch)
    return batches


def _write_one_file(
    filename: str,
    content: str,
    test_dir: Path,
    new_names: list[str],
) -> None:
    """Write content to a single .cpp file and record its name."""
    outpath = test_dir / f"{filename}.cpp"
    outpath.write_text(content, encoding="utf-8")
    new_names.append(filename)
