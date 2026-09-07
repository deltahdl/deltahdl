---
name: naming-the-report-in-a-rejection-test
description: A test expecting a source rejected names the report with ReportedError — message substring, line and exact Subclause text.
metadata:
  type: feedback
---

# Naming the report in a test that expects a rejection

A test that expects a source rejected names the report with `ReportedError` in `lib/cpp/test_helpers/helpers_reported_error.h`: a substring of the message, the line of the test's own source the report stands at, and the exact `Subclause("…")` text the emission site passes. Use `ReportedWarning` where the rule is enforced with a warning.

**Why:** Assertions that only ask whether something failed — `HasErrors()`, `has_errors`, `ParseOk`, `CompileOutcome::kFailed`, a `diags` count or emptiness check, `ErrorCount()`, a `LexWithDiag` error flag — pass when a different rule fired and when the source never reached the construct under test. `FindDiag` and `r.diags.front()` select the wrong report as readily as the right one. So the test goes green while covering nothing.

**How to apply:** Name the report. Leave two kinds of site alone: one that varies only the construct under test while holding the rest of the source fixed, and one whose rule nothing reports, which needs an issue about the program instead — see [filing-what-a-session-finds](filing-what-a-session-finds.md). A test asserting a source was accepted is sound as it stands.
