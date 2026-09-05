# Assert which rule a rejection enforced

A test that hands deltahdl an illegal source names the report, and it names three things about it: the message, the line, and the subclause of IEEE 1800-2023 the report enforces. Write that as one call to `ReportedError`, declared in `lib/cpp/test_helpers/helpers_reported_error.h`:

```cpp
EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                          "kill() shall only target a process", 5, "9.7"));
```

`EXPECT_TRUE(f.diag.HasErrors())` is what this replaces, along with `EXPECT_TRUE(f.has_errors)`, `EXPECT_FALSE(ParseOk(...))` and `EXPECT_EQ(..., CompileOutcome::kFailed)`. Every one of those is satisfied by any rejection.

So is every count. `ASSERT_EQ(r.diags.size(), 1u)`, `ASSERT_FALSE(r.diags.empty())` and `EXPECT_EQ(f.diag.ErrorCount(), 1U)` state how many reports a run made and nothing about which rule any of them enforced, and a count goes red when a second report is added for an unrelated reason. `EXPECT_TRUE(errors)`, off an `auto [tokens, errors] = LexWithDiag(…)` binding, is the same claim with no member, helper or error word in the assertion at all; write the case against `LexDiagnostics` in `lib/cpp/test_fixtures/fixture_lexer.h` instead, which hands back the reports themselves.

Two more shapes name the rule without naming all three of it. `FindDiag` selects a report by its message alone and matches a warning as readily as an error, so a body that binds one and asserts `d->subclause` leaves the line unstated and a second breach of the same rule on a different line satisfies it. `r.diags.front().subclause` reads whichever report the run wrote first, which the comment on `FindDiag` in `lib/cpp/test_fixtures/fixture_parser.h` documents as the wrong one when a source is rejected twice. The four `FindDiag` declarations stay: they serve the acceptance form `EXPECT_EQ(FindDiag(f, "…"), nullptr)`.

`ReportedWarning` in the same header takes the same three arguments and answers them of a warning, for a rule the program enforces with one. §23.3.2.1 has the binder warn about an ordered port connection past the last port rather than reject the source, so a case reading that report through `ReportedError` would fail whatever the run recorded.

## What that costs

A test written for one rule passes when a different rule fired, and passes when the source never reached the construct the test is about.

That has happened. `SinglePassPrecompile.DescriptionClaimedByTwoLibrariesNamesBothInItsDiagnostic` in `test/src/unit/test_parser_subclause_33_05_01.cpp` covers §33.5.1 and handed the compiler `module cell;` until commit `28234b4ac`. Annex B, Table B.1 reserves `cell`, so the source never parsed and the compile failed on the reserved word rather than on the ambiguity between two libraries the test was written for. `CompileOutcome::kFailed` is the value for both, so the test passed while covering nothing.

## The three arguments

**The subclause is the exact text of the emission site's `Subclause("…")`.** Copy it from the site; do not derive it from the test file's name. `Diagnostic::message` does not carry it — `DiagEngine::Emit` in `src/common/diagnostic.cpp` appends `(§x.y)` only when it writes the report to stderr — so no section sign belongs in the message argument.

**The message is matched as a substring, and the substring has to be one no other report produces.** A report assembled while the design runs carries a name or a value that the literal at the emission site does not hold: `Preprocessor::RejectInsideDesignElement` in `src/preprocessor/preprocessor_lines.cpp` builds its sentence from the directive it read and `" illegal inside a design element"`. So the argument is a literal fragment rather than the assembled sentence. Nothing checks that the fragment is distinctive, and a fragment several reports share proves as little as the count it replaced.

**The line is the line of the test's own source string**, counting the first line of the literal as line 1, and it is the line the report's `SourceLoc` points at. Read the emission site to see which node it passes — `expr->range.start`, `stmt->range.start`, `item->loc` — then find that construct in the source. The subclause says which rule was enforced and the line says where the source broke it, which is what tells two breaches of one rule apart.

The three are one call rather than three expectations because a test that names two of them and forgets the third still reads as complete.

## What not to convert

**A test that holds the source fixed and varies only the construct under test.** A rejection there is attributable without reading the report, because nothing else in the source changed. `KeywordListParsing.NoReservedWordCanNameAVariable` sweeps all 248 words of Table B.1 through one `VarDecl` template, and converting it would assert 248 times what one report says.

**A test that asserts a source was accepted.** The claim there is that nothing was reported, so there is no report to name, and `HasErrors()` is the right member for it.

**A test that reports the diagnostic itself.** The eleven cases in `test/src/unit/test_non_lrm_diagnostic.cpp` call `DiagEngine::Error` and `DiagEngine::Warning` and read the record back, so the report they check is one the case wrote rather than one a source provoked, and no rule of the standard is in question.

**A site whose report does not exist.** Where the standard states a rule and no stage reports it, the test is passing on some other rejection. Leave the assertion alone and open an issue about the program in the six-section form; converting it would only move the silence.

## Where the assertion lives

`ReportedError` takes `const std::vector<Diagnostic>&` rather than a fixture, so it serves every component: a simulator test passes `f.diag.Diagnostics()` and a parser test passes the `diags` that `ParseResult` in `lib/cpp/test_fixtures/fixture_parser.h` copied. The four `FindDiag` declarations, in that file and in `fixture_elaborator.h`, `fixture_simulator.h` and `fixture_synthesizer.h`, predate it and select a report by message alone; a new test names all three instead.

Related: [test-driven-development](test-driven-development.md) for when the test is written, [how-issues-are-written](how-issues-are-written.md) for the issue a missing report needs, and [verifying-through-ci](verifying-through-ci.md) for reading the result.
