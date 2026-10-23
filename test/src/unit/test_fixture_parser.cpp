// Tests over the unread-error check of lib/cpp/test_fixtures/fixture_parser.h.
//
// A ParseResult fails a parser case that was handed a source the parser
// rejected and never read has_errors or diags, so a defect in it either lets
// such a case go on passing or fails cases that did read them. The engine that
// recorded the errors is a local of the call that ran the parser and is gone
// before the case runs, so the record and whether the case read it both live
// on the result, and the cases below drive the result alone.
//
// As in test_fixture_diagnosed.cpp, a case asserting that the result stayed
// quiet needs no macro saying so: the result reports through ADD_FAILURE as it
// is destroyed, which fails whichever case is running. A case asserting that
// it did report builds the result inside a function of its own and hands the
// call to EXPECT_NONFATAL_FAILURE, from gtest/gtest-spi.h, so the destruction
// falls inside the statement the macro watches and exactly one report is
// expected of it.

#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A data declaration with no terminating semicolon, which the parser rejects
// once, at `endmodule` on line 3, under §6.8.
constexpr const char* kRejectedSrc =
    "module m;\n"
    "  logic x\n"
    "endmodule\n";

constexpr const char* kUnreadReport =
    "the source drew an error the case never read";

void ParseARejectedSourceNobodyReads() { auto r = Parse(kRejectedSrc); }

TEST(ParseResultRead, AnErrorNeverReadFailsTheCase) {
  EXPECT_NONFATAL_FAILURE(ParseARejectedSourceNobodyReads(), kUnreadReport);
}

// The report has to say which input to look at and what was wrong with it, or
// whoever reads the failure is sent to the harness instead of to the case.
TEST(ParseResultRead, TheReportNamesTheSourceAndTheErrorItDrew) {
  EXPECT_NONFATAL_FAILURE(ParseARejectedSourceNobodyReads(), "  logic x\n");
  EXPECT_NONFATAL_FAILURE(ParseARejectedSourceNobodyReads(),
                          "line 3: expected ';', got 'endmodule'");
}

// The other two entry points record their run the same way Parse does.
void PreprocessARejectedSourceNobodyReads() {
  auto r = ParseWithPreprocessor(kRejectedSrc);
}

void ParseARejectedLibraryNobodyReads() { auto r = ParseLibrary(kRejectedSrc); }

TEST(ParseResultRead, EveryEntryPointFailsAnErrorNeverRead) {
  EXPECT_NONFATAL_FAILURE(PreprocessARejectedSourceNobodyReads(),
                          kUnreadReport);
  EXPECT_NONFATAL_FAILURE(ParseARejectedLibraryNobodyReads(), kUnreadReport);
}

// PreprocessAndParse, in fixture_preprocessor_timescale.h, hands over a
// ParseResult as well, with the preprocessor's global precision beside it, and
// is held to the same read.
void PreprocessAndParseARejectedSourceNobodyReads() {
  auto r = PreprocessAndParse(kRejectedSrc);
}

TEST(ParseResultRead, APreprocessedParseFailsAnErrorNeverRead) {
  EXPECT_NONFATAL_FAILURE(PreprocessAndParseARejectedSourceNobodyReads(),
                          kUnreadReport);
  EXPECT_NONFATAL_FAILURE(PreprocessAndParseARejectedSourceNobodyReads(),
                          "  logic x\n");
}

void MoveAnUnreadPreprocessedParse() {
  auto first = PreprocessAndParse(kRejectedSrc);
  PreprocessedParseResult second(std::move(first));
}

TEST(ParseResultRead, AMovedPreprocessedParseRaisesItOnce) {
  EXPECT_NONFATAL_FAILURE(MoveAnUnreadPreprocessedParse(), kUnreadReport);
}

// PreprocessTimescale, in the same header, hands over the timescale state the
// preprocessor ended in on a record of the same kind. A `timescale whose unit
// is no unit name is rejected once, on line 1, under §22.7, and still leaves a
// state behind.
constexpr const char* kRejectedTimescaleSrc = "`timescale 1xx / 1ns\n";

void PreprocessARejectedTimescaleNobodyReads() {
  auto r = PreprocessTimescale(kRejectedTimescaleSrc);
}

TEST(RecordedRunRead, APreprocessedTimescaleFailsAnErrorNeverRead) {
  EXPECT_NONFATAL_FAILURE(PreprocessARejectedTimescaleNobodyReads(),
                          kUnreadReport);
  EXPECT_NONFATAL_FAILURE(PreprocessARejectedTimescaleNobodyReads(),
                          "`timescale 1xx / 1ns\n");
}

TEST(RecordedRunRead, NamingAPreprocessedTimescalesReportDischargesIt) {
  auto r = PreprocessTimescale(kRejectedTimescaleSrc);

  EXPECT_TRUE(ReportedError(r.diags, "invalid `timescale unit", 1, "22.7"));
}

void MoveAnUnreadPreprocessedTimescale() {
  auto first = PreprocessTimescale(kRejectedTimescaleSrc);
  PreprocTimescaleResult second(std::move(first));
}

TEST(RecordedRunRead, AMovedPreprocessedTimescaleRaisesItOnce) {
  EXPECT_NONFATAL_FAILURE(MoveAnUnreadPreprocessedTimescale(), kUnreadReport);
}

// Parses the rejected source and then reads the record with `read`. The reads
// below take the answer without asserting it, so that none of them claims the
// source was rejected without naming the report.
void ParseThenRead(void (*read)(const ParseResult&)) {
  auto r = Parse(kRejectedSrc);
  read(r);
}

// has_errors is read through its conversion to bool, which an assertion macro,
// an `if` and a `!` all go through.
TEST(ParseResultRead, ReadingHasErrorsDischargesIt) {
  ParseThenRead([](const ParseResult& r) {
    static_cast<void>(static_cast<bool>(r.has_errors));
  });
  ParseThenRead([](const ParseResult& r) { static_cast<void>(!r.has_errors); });
}

TEST(ParseResultRead, NamingTheReportDischargesIt) {
  auto r = Parse(kRejectedSrc);

  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "6.8"));
}

// Each way a case reaches diags discharges the obligation, as reading
// has_errors does, so a case that read the rejection through any of them is
// not called unread.
TEST(ParseResultRead, AnyReadOfTheDiagnosticsDischargesIt) {
  ParseThenRead(
      [](const ParseResult& r) { static_cast<void>(r.diags.size()); });
  ParseThenRead(
      [](const ParseResult& r) { static_cast<void>(r.diags.empty()); });
  ParseThenRead([](const ParseResult& r) {
    for (const auto& d : r.diags) static_cast<void>(d);
  });
  ParseThenRead([](const ParseResult& r) {
    const std::vector<Diagnostic>& all = r.diags;
    static_cast<void>(all);
  });
  ParseThenRead(
      [](const ParseResult& r) { static_cast<void>(FindDiag(r, "expected")); });
}

// ParseOk and ParseWithPreprocessorOk read has_errors on their caller's
// behalf, so the answer they give is the case's read.
TEST(ParseResultRead, TheAcceptanceHelpersReadOnTheCallersBehalf) {
  static_cast<void>(ParseOk(kRejectedSrc));
  static_cast<void>(ParseWithPreprocessorOk(kRejectedSrc));
}

// A case that a defect of deltahdl's fails is excused beside the issue filed
// for it, as an elaborator case is through Diagnosed::Excuse.
TEST(ParseResultRead, AnExcusedResultRaisesNothing) {
  auto r = Parse(kRejectedSrc);

  r.has_errors.Excuse();
}

TEST(ParseResultRead, AnAcceptedSourceNeverReadRaisesNothing) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "endmodule\n");
}

// A helper that runs the parser on an engine of its own records the answer by
// assigning it, and the assignment leaves the read owed, as recording the run
// does.
void AssignAnAnswerNobodyReads() {
  ParseResult r;
  r.has_errors = true;
}

TEST(ParseResultRead, AnAssignedAnswerIsNoRead) {
  EXPECT_NONFATAL_FAILURE(AssignAnAnswerNobodyReads(), kUnreadReport);
}

// EXPECT_NONFATAL_FAILURE expects exactly one report, so a move that left the
// obligation on both results fails here as much as one that dropped it.
void MoveAnUnreadResult() {
  auto first = Parse(kRejectedSrc);
  ParseResult second(std::move(first));
}

void AssignAnUnreadResult() {
  ParseResult r;
  r = Parse(kRejectedSrc);
}

TEST(ParseResultRead, AMoveCarriesTheObligationAndRaisesItOnce) {
  EXPECT_NONFATAL_FAILURE(MoveAnUnreadResult(), kUnreadReport);
  EXPECT_NONFATAL_FAILURE(AssignAnUnreadResult(), kUnreadReport);
}

TEST(ParseResultRead, AReadBeforeAMoveTravelsWithIt) {
  auto first = Parse(kRejectedSrc);
  static_cast<void>(static_cast<bool>(first.has_errors));

  ParseResult second(std::move(first));
}

}  // namespace
