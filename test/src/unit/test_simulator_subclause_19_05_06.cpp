#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, IllegalBinsExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin bad;
  bad.name = "illegal";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0xFF};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 1}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(Coverage, IllegalValuesRemovedFromStateBin) {
  EXPECT_EQ(CoverageDB::RemoveIllegalValues({5, 7, 8, 7, 9}, {7, 8}),
            (std::vector<int64_t>{5, 9}));
  EXPECT_EQ(CoverageDB::RemoveIllegalValues({1, 2, 3}, {4}),
            (std::vector<int64_t>{1, 2, 3}));
}

TEST(Coverage, IllegalValuesRemovedAfterDistribution) {
  auto distributed = CoverageDB::DistributeValues({1, 2, 3, 4, 5, 6}, 3);
  std::vector<int64_t> illegal = {3, 4};
  std::vector<std::vector<int64_t>> remaining;
  remaining.reserve(distributed.size());
  for (const auto& bin : distributed) {
    remaining.push_back(CoverageDB::RemoveIllegalValues(bin, illegal));
  }
  EXPECT_EQ(remaining, (std::vector<std::vector<int64_t>>{{1, 2}, {}, {5, 6}}));
}

TEST(Coverage, IllegalRemovalCanEmptyStateBin) {
  EXPECT_TRUE(CoverageDB::RemoveIllegalValues({1, 2, 3}, {3, 1, 2}).empty());
}

TEST(Coverage, EmptyIllegalSetLeavesStateBinUnchanged) {
  EXPECT_EQ(CoverageDB::RemoveIllegalValues({4, 2, 4, 6}, {}),
            (std::vector<int64_t>{4, 2, 4, 6}));
}

TEST(Coverage, CoveredTransitionRemovedWhenContainsIllegal) {
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({2, 3}, {2, 3}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({2, 9, 3}, {2, 3}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3, 4}, {5, 6}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({2, 3}, {1, 2, 3, 4}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3}, {}));
}

TEST(Coverage, IllegalValueDoesNotAffectTransition) {
  EXPECT_FALSE(CoverageDB::IllegalValueAffectsTransition(3, {1, 2, 3, 4}));
  EXPECT_FALSE(CoverageDB::IllegalValueAffectsTransition(7, {7, 7}));
}

TEST(Coverage, IllegalTransitionMustBeBounded) {
  EXPECT_TRUE(CoverageDB::IllegalTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kConsecutive)));
  EXPECT_FALSE(CoverageDB::IllegalTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kGoto)));
  EXPECT_FALSE(CoverageDB::IllegalTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(
          TransitionRepeatKind::kNonconsecutive)));
}

TEST(Coverage, IllegalTakesPrecedenceOverOtherBins) {
  EXPECT_TRUE(CoverageDB::IllegalTakesPrecedence(true));
  EXPECT_TRUE(CoverageDB::IllegalTakesPrecedence(false));
}

TEST(Coverage, IllegalValueOccurrenceIssuesRuntimeError) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin ib;
  ib.name = "bad";
  ib.kind = CoverBinKind::kIllegal;
  ib.values = {0xFF};
  CoverageDB::AddBin(cp, ib);

  db.Sample(g, {{"addr", 0xFF}});

  EXPECT_EQ(cp->illegal_violations, 1u);
  EXPECT_EQ(cp->bins[0].hit_count, 0u);
}

TEST(Coverage, LegalValueRaisesNoIllegalViolation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin legal;
  legal.name = "legal";
  legal.values = {1};
  CoverageDB::AddBin(cp, legal);
  CoverBin bad;
  bad.name = "bad";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0xFF};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 1}});

  EXPECT_EQ(cp->illegal_violations, 0u);
  EXPECT_EQ(cp->bins[0].hit_count, 1u);
}

TEST(Coverage, IllegalValueInAnotherBinStillErrorsAndIsNotCounted) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin legal;
  legal.name = "legal";
  legal.values = {7};
  CoverageDB::AddBin(cp, legal);
  CoverBin bad;
  bad.name = "bad";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {7};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 7}});

  EXPECT_EQ(cp->illegal_violations, 1u);
  EXPECT_EQ(cp->bins[0].hit_count, 0u);
}

TEST(Coverage, IllegalStateValueDoesNotSuppressTransitionThroughIt) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");

  CoverBin trans;
  trans.name = "seq";
  trans.kind = CoverBinKind::kTransition;
  trans.transitions = {{1, 2, 3, 4}};
  CoverageDB::AddBin(cp, trans);

  CoverBin bad;
  bad.name = "bad_state";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {3};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"s", 1}});
  db.Sample(g, {{"s", 2}});
  db.Sample(g, {{"s", 3}});
  db.Sample(g, {{"s", 4}});

  EXPECT_EQ(cp->illegal_violations, 1u);
  EXPECT_EQ(cp->bins[0].hit_count, 1u);
}

void ExpectIllegalTransitionOutcome(std::initializer_list<int64_t> values,
                                    uint32_t violations, uint32_t hits) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");
  CoverBin bad;
  bad.name = "bad_trans";
  bad.kind = CoverBinKind::kIllegal;
  bad.transitions = {{4, 5, 6}};
  CoverageDB::AddBin(cp, bad);

  for (int64_t v : values) db.Sample(g, {{"s", v}});

  EXPECT_EQ(cp->illegal_violations, violations);
  EXPECT_EQ(cp->bins[0].hit_count, hits);
}

TEST(Coverage, IllegalTransitionOccurrenceIssuesRuntimeError) {
  ExpectIllegalTransitionOutcome({4, 5, 6}, 1u, 0u);
}

TEST(Coverage, IllegalTransitionBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");

  CoverBin good;
  good.name = "good_trans";
  good.kind = CoverBinKind::kTransition;
  good.transitions = {{1, 2}};
  CoverageDB::AddBin(cp, good);

  CoverBin bad;
  bad.name = "bad_trans";
  bad.kind = CoverBinKind::kIllegal;
  bad.transitions = {{7, 8}};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"s", 1}});
  db.Sample(g, {{"s", 2}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(Coverage, NonMatchingSequenceRaisesNoIllegalTransitionViolation) {
  ExpectIllegalTransitionOutcome({4, 5, 9}, 0u, 0u);
}

TEST(CovergroupInstanceSim, IllegalBinHitIsRunTimeError) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [3:0] v;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins ok = {[4:9]}; illegal_bins bad "
                       "= {1, 2, 3}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 5; c.sample();\n"
                       "    v = 2; c.sample();\n"
                       "    $display(\"done\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "done\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sampled value 2 of coverpoint 'v' falls in an "
                            "illegal bin",
                            9, "19.5.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CovergroupInstanceSim, IllegalTransitionRemovesASequenceContainingIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [2:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins t = (1 => 2 => 3 => 4);\n"
                       "      bins u = (2 => 4); bins one = {1};\n"
                       "      illegal_bins x = (2 => 3); }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 1; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
