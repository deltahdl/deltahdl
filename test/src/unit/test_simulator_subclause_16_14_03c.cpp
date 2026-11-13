#include <gtest/gtest.h>

#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"
#include "simulator/cover_results.h"
#include "simulator/cover_statement.h"

using namespace delta;

namespace {

constexpr const char* kCoverSignals =
    "  logic clk = 0, req = 0, ack = 0;\n"
    "  int marker = -1, nba = -1;\n"
    "  always #5 clk = ~clk;\n"
    "  always @(posedge clk) marker = $time;\n"
    "  always @(posedge clk) nba <= $time;\n"
    "  initial begin #10 req = 1; #10 req = 0; ack = 1; #20 ack = 0; end\n"
    "  initial #60 $finish;\n";

constexpr PlacedDesign kCoverDesign = {
    kCoverSignals, "(input logic clk, req, ack)", "clk, req, ack"};

constexpr const char* kCoverItems =
    "cp: cover property (@(posedge clk) req ##[1:2] ack) "
    "$display(\"prop %0t %0d %0d\", $time, t.marker, t.nba);\n"
    "cs: cover sequence (@(posedge clk) req ##[1:2] ack) "
    "$display(\"seq %0t %0d %0d\", $time, t.marker, t.nba);\n";

constexpr const char* kEveryPassStatement =
    "prop 25 25 25\nseq 25 25 25\nseq 35 35 35\n";

TEST(CoverPassRegion,
     EachPassStatementSeesItsOwnStepsActiveAndNbaWritesInEachPlace) {
  ExpectPlacedLinesInEachPlace(kCoverDesign,
                               {kCoverItems, kEveryPassStatement, nullptr});
}

struct CoverControlRow {
  const char* controls;
  const char* lines;
};

constexpr CoverControlRow kCoverControls[] = {
    {"$assertpassoff;", ""},
    {"$assertcontrol(7);", ""},
    {"$assertcontrol(7, 1, 2);", ""},
    {"$assertoff;", ""},
    {"$assertpassoff; #30 $assertpasson;", "seq 35 35 35\n"},
    {"$assertcontrol(7, 1, 1);", kEveryPassStatement},
    {"$assertcontrol(7, 1, 4);", kEveryPassStatement},
    {"$assertfailoff;", kEveryPassStatement},
    {"$assertvacuousoff;", kEveryPassStatement}};

TEST(CoverPassControl,
     EachActionControlTaskGovernsThePassStatementInEachPlace) {
  for (const CoverControlRow& row : kCoverControls) {
    SCOPED_TRACE(row.controls);
    ExpectPlacedLinesInEachPlace(
        kCoverDesign, {kCoverItems, row.lines, nullptr}, "", row.controls);
  }
}

struct CoverCounts {
  uint64_t property_attempted;
  uint64_t property_succeeded;
  uint64_t property_vacuous;
  uint64_t sequence_attempted;
  uint64_t sequence_matched;
  bool operator==(const CoverCounts&) const = default;
};

std::ostream& operator<<(std::ostream& os, const CoverCounts& counts) {
  return os << "property " << counts.property_attempted << "/"
            << counts.property_succeeded << "/" << counts.property_vacuous
            << ", sequence " << counts.sequence_attempted << "/"
            << counts.sequence_matched;
}

CoverCounts CountsOf(const std::vector<ConcurrentCoverResult>& results) {
  CoverCounts counts{};
  for (const ConcurrentCoverResult& result : results) {
    if (result.category == CoverStatementCategory::kProperty) {
      counts.property_attempted += result.attempted;
      counts.property_succeeded += result.succeeded;
      counts.property_vacuous += result.vacuous;
    } else {
      counts.sequence_attempted += result.attempted;
      counts.sequence_matched += result.matched;
    }
  }
  return counts;
}

TEST(CoverResults, EachPlaceCountsAttemptsSuccessesAndEveryMatch) {
  for (const char* place : kAssertionPlaces) {
    SCOPED_TRACE(place);
    SimFixture f;
    RunPlaced(PlacedSource(kCoverDesign, place, kCoverItems), f);
    uint64_t attempts = std::string(place) == "initial" ? 1 : 6;
    EXPECT_EQ(CountsOf(f.ctx.ConcurrentCovers().Results()),
              (CoverCounts{attempts, 1, 0, attempts, 2}));
  }
}

}  // namespace
