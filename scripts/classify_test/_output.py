"""Output and summary formatting for classify_test."""

import textwrap


def _format_clause(clause):
    """Format a clause for display."""
    if clause is None:
        return "(parse error)"
    if clause.startswith("non-lrm:"):
        tag = clause[len("non-lrm:"):].upper().replace("_", " ")
        return f"Non-LRM {tag}"
    return f"\u00a7{clause}"


def _wrap(label, value):
    """Wrap a labeled line to 80 chars with 2-space continuation indent."""
    return textwrap.fill(
        value, width=80,
        initial_indent=f"  {label}: ",
        subsequent_indent="  ",
    )


_PREFIX_TO_STAGE = {
    "test_preprocessor_": "preprocessor",
    "test_lexer_": "lexer",
    "test_parser_": "parser",
    "test_elaborator_": "elaborator",
    "test_simulator_": "simulator",
    "test_synthesizer_": "synthesizer",
}


def print_classification_table(tests):
    """Print the classification results as sub-reports."""
    for i, t in enumerate(tests):
        print(_wrap("Test", f"{t.test_name}()"))
        print(_wrap("Clause", _format_clause(t.clause)))
        print(_wrap("Rationale", t.rationale or ""))
        stage = _PREFIX_TO_STAGE.get(t.prefix, t.prefix or "")
        print(_wrap("Stage", stage))
        print(_wrap("Stage rationale",
                     getattr(t, "prefix_rationale", "") or ""))
        if i < len(tests) - 1:
            print("  ----")


def print_summary(
    to_create, to_merge, test_name, source_is_target, **kwargs,
):
    """Print the because-driven summary of what was done."""
    n_kept = kwargs.get("n_kept", 0)
    n_removed = kwargs.get("n_removed", 0)
    dry_run = kwargs.get("dry_run", False)

    def _v(past):
        """Return past future perfect tense if dry_run, else past."""
        if not dry_run:
            return past
        return f"Would have {past[0].lower()}{past[1:]}"

    print("\n  SUMMARY")
    def _pl(count, word):
        return f"{count} {word}{'s' if count != 1 else ''}"

    if not to_create and not to_merge and source_is_target:
        if n_kept:
            print(f"  - {_v('Kept')} {_pl(n_kept, 'test')} in"
                  f" `{test_name}.cpp` because"
                  f" {'it belongs' if n_kept == 1 else 'they belong'}"
                  " there.")
        if n_removed:
            rem = "to remove" if dry_run else "removed"
            print(f"  - {_pl(n_removed, 'duplicate')} {rem}.")
        return
    for filename, _clause, tests in to_create:
        print(f"  - {_v('Created')} `{filename}.cpp` because"
              f" {_pl(len(tests), 'test')}"
              f" {'belongs' if len(tests) == 1 else 'belong'}"
              " there but the file did not exist.")
        print(f"  - {_v('Moved')} {_pl(len(tests), 'test')} to"
              f" `{filename}.cpp` because that's where"
              f" {'it belongs' if len(tests) == 1 else 'they belong'}.")
    for merge_path, tests in to_merge:
        print(f"  - {_v('Moved')} {_pl(len(tests), 'test')} to"
              f" `{merge_path.name}` because that's where"
              f" {'it belongs' if len(tests) == 1 else 'they belong'}.")
    if source_is_target and n_kept:
        print(f"  - {_v('Kept')} {_pl(n_kept, 'test')} in"
              f" `{test_name}.cpp` because"
              f" {'it belongs' if n_kept == 1 else 'they belong'}"
              " there.")
    if not source_is_target and not kwargs.get("n_others", 0):
        print(f"  - {_v('Deleted')} `{test_name}.cpp` because"
              " all its tests were moved elsewhere.")
        print(f"  - {_v('Updated')} `CMakeLists.txt` because"
              f" `{test_name}` was removed.")
    else:
        print(f"  - {_v('Updated')} `CMakeLists.txt` because"
              " new test targets were added.")
