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

TEST(ParseResultRead, TheReportNamesTheSourceAndTheErrorItDrew) {
  EXPECT_NONFATAL_FAILURE(ParseARejectedSourceNobodyReads(), "  logic x\n");
  EXPECT_NONFATAL_FAILURE(ParseARejectedSourceNobodyReads(),
                          "line 3: expected ';', got 'endmodule'");
}

void PreprocessARejectedSourceNobodyReads() {
  auto r = ParseWithPreprocessor(kRejectedSrc);
}

void ParseARejectedLibraryNobodyReads() { auto r = ParseLibrary(kRejectedSrc); }

TEST(ParseResultRead, EveryEntryPointFailsAnErrorNeverRead) {
  EXPECT_NONFATAL_FAILURE(PreprocessARejectedSourceNobodyReads(),
                          kUnreadReport);
  EXPECT_NONFATAL_FAILURE(ParseARejectedLibraryNobodyReads(), kUnreadReport);
}

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

void ParseThenRead(void (*read)(const ParseResult&)) {
  auto r = Parse(kRejectedSrc);
  read(r);
}

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

TEST(ParseResultRead, TheAcceptanceHelpersReadOnTheCallersBehalf) {
  static_cast<void>(ParseOk(kRejectedSrc));
  static_cast<void>(ParseWithPreprocessorOk(kRejectedSrc));
}

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

void AssignAnAnswerNobodyReads() {
  ParseResult r;
  r.has_errors = true;
}

TEST(ParseResultRead, AnAssignedAnswerIsNoRead) {
  EXPECT_NONFATAL_FAILURE(AssignAnAnswerNobodyReads(), kUnreadReport);
}

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
