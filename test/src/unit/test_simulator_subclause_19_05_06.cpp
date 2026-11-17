#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "common/diagnostic.h"
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

struct IllegalRun {
  std::string out;
  std::vector<Diagnostic> diags;
  uint32_t errors = 0;
};

IllegalRun RunIllegal(const std::string& design) {
  SimFixture f;
  IllegalRun run;
  run.out = RunCapture(design, f);
  run.diags = f.diag.Diagnostics();
  run.errors = f.diag.ErrorCount();
  return run;
}

bool ReportsValueAt(const IllegalRun& run, const std::string& point,
                    int64_t value, uint32_t line) {
  return ReportedError(run.diags,
                       "sampled value " + std::to_string(value) +
                           " of coverpoint '" + point +
                           "' falls in an illegal bin",
                       line, "19.5.6");
}

TEST(IllegalBinsSim, IllegalValuesLeaveTheBinsAfterTheValuesAreSplit) {
  IllegalRun run = RunIllegal(
      "module top;\n"
      "  bit [2:0] v; int n, t;\n"
      "  covergroup cg;\n"
      "    pa: coverpoint v { bins s[2] = {[0:3]};\n"
      "      illegal_bins bad = {0, 1}; }\n"
      "    pb: coverpoint v { bins x = {1, 2}; bins y = {3};\n"
      "      illegal_bins bad = {1, 2}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    v = 2; c.sample(); v = 3; c.sample();\n"
      "    void'(c.pa.get_inst_coverage(n, t));\n"
      "    $display(\"pa %0d %0d\", n, t);\n"
      "    void'(c.pb.get_inst_coverage(n, t));\n"
      "    $display(\"pb %0d %0d\", n, t);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run.out, "pa 1 1\npb 1 1\n");
  EXPECT_TRUE(ReportsValueAt(run, "pb", 2, 11));
  EXPECT_EQ(run.errors, 1u);
}

TEST(IllegalBinsSim, AnIllegalValueLeavesATransitionThroughIt) {
  IllegalRun run = RunIllegal(
      "module top;\n"
      "  bit [2:0] v; int n, t;\n"
      "  covergroup cg;\n"
      "    coverpoint v { bins t = (1 => 2); bins o = {5};\n"
      "      illegal_bins bad = {2}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    v = 1; c.sample();\n"
      "    v = 2; c.sample();\n"
      "    void'(c.get_inst_coverage(n, t));\n"
      "    $display(\"%0d %0d\", n, t);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run.out, "1 2\n");
  EXPECT_TRUE(ReportsValueAt(run, "v", 2, 10));
  EXPECT_EQ(run.errors, 1u);
}

TEST(IllegalBinsSim, AnIllegalTransitionFromSourceIsARunTimeError) {
  IllegalRun run = RunIllegal(
      "module top;\n"
      "  bit [2:0] v; int n, t;\n"
      "  covergroup cg;\n"
      "    coverpoint v { bins o = {0}; illegal_bins bad = (1 => 2); }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    v = 1; c.sample(); v = 2; c.sample();\n"
      "    v = 0; c.sample(); v = 2; c.sample();\n"
      "    v = 1; c.sample();\n"
      "    v = 2; c.sample();\n"
      "    void'(c.get_inst_coverage(n, t));\n"
      "    $display(\"%0d %0d\", n, t);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run.out, "1 1\n");
  EXPECT_TRUE(ReportsValueAt(run, "v", 2, 8));
  EXPECT_TRUE(ReportsValueAt(run, "v", 2, 11));
  EXPECT_EQ(run.errors, 2u);
}

TEST(IllegalBinsSim, AnIllegalBinOutranksIgnoreBinsAndOtherBins) {
  IllegalRun run = RunIllegal(
      "module top;\n"
      "  bit [2:0] v; int n, t;\n"
      "  covergroup cg;\n"
      "    pa: coverpoint v { bins b[] = {[0:3]}; ignore_bins ig = {1};\n"
      "      illegal_bins bad = {1}; }\n"
      "    pb: coverpoint v { bins ok = {[0:3]}; illegal_bins bad = {2}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    v = 1; c.sample();\n"
      "    v = 2; c.sample();\n"
      "    void'(c.pa.get_inst_coverage(n, t));\n"
      "    $display(\"pa %0d %0d\", n, t);\n"
      "    void'(c.pb.get_inst_coverage(n, t));\n"
      "    $display(\"pb %0d %0d\", n, t);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run.out, "pa 1 3\npb 1 1\n");
  EXPECT_TRUE(ReportsValueAt(run, "pa", 1, 10));
  EXPECT_TRUE(ReportsValueAt(run, "pb", 2, 11));
  EXPECT_EQ(run.errors, 2u);
}

TEST(IllegalBinsSim, EveryFormOfIllegalBinReportsItsValues) {
  IllegalRun run = RunIllegal(
      "module top;\n"
      "  bit [2:0] v; int n, t;\n"
      "  int arr[2] = '{1, 5};\n"
      "  covergroup c1;\n"
      "    pa: coverpoint v { bins b[] = {[0:7]};\n"
      "      wildcard illegal_bins bad = {3'b1??}; }\n"
      "  endgroup\n"
      "  covergroup c2;\n"
      "    pb: coverpoint v { bins b[] = {[0:7]};\n"
      "      illegal_bins bad[] = {[2:3], 6}; }\n"
      "  endgroup\n"
      "  covergroup c3;\n"
      "    pc: coverpoint v { bins b[] = {[0:7]};\n"
      "      illegal_bins bad = {[0:7]} with (item % 2 == 1); }\n"
      "  endgroup\n"
      "  covergroup c4;\n"
      "    pd: coverpoint v { bins b[] = {[0:7]}; illegal_bins bad = arr; }\n"
      "  endgroup\n"
      "  c1 g1 = new; c2 g2 = new; c3 g3 = new; c4 g4 = new;\n"
      "  initial begin\n"
      "    v = 3; g1.sample();\n"
      "    v = 5; g1.sample();\n"
      "    v = 4; g2.sample();\n"
      "    v = 6; g2.sample();\n"
      "    v = 4; g3.sample();\n"
      "    v = 3; g3.sample();\n"
      "    v = 4; g4.sample();\n"
      "    v = 5; g4.sample();\n"
      "    void'(g1.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, t);\n"
      "    void'(g2.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, t);\n"
      "    void'(g3.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, t);\n"
      "    void'(g4.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, t);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run.out, "1 4\n1 5\n1 4\n1 6\n");
  EXPECT_TRUE(ReportsValueAt(run, "pa", 5, 22));
  EXPECT_TRUE(ReportsValueAt(run, "pb", 6, 24));
  EXPECT_TRUE(ReportsValueAt(run, "pc", 3, 26));
  EXPECT_TRUE(ReportsValueAt(run, "pd", 5, 28));
  EXPECT_EQ(run.errors, 4u);
}

TEST(IllegalBinsSim, DISABLED_ADefaultIllegalBinReportsWhatItCatches) {
  IllegalRun run = RunIllegal(
      "module top;\n"
      "  bit [2:0] v;\n"
      "  covergroup c1;\n"
      "    pa: coverpoint v { bins a = {1}; illegal_bins rest = default; }\n"
      "  endgroup\n"
      "  covergroup c2;\n"
      "    pb: coverpoint v { bins t = (1 => 2);\n"
      "      illegal_bins rest = default sequence; }\n"
      "  endgroup\n"
      "  c1 g1 = new; c2 g2 = new;\n"
      "  initial begin\n"
      "    v = 1; g1.sample();\n"
      "    v = 2; g1.sample();\n"
      "    v = 1; g2.sample(); v = 2; g2.sample();\n"
      "    v = 4; g2.sample();\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run.out, "done\n");
  EXPECT_TRUE(ReportsValueAt(run, "pa", 2, 13));
  EXPECT_TRUE(ReportsValueAt(run, "pb", 4, 15));
  EXPECT_EQ(run.errors, 2u);
}

TEST(IllegalBinsSim, IllegalBinsReportInEveryPlace) {
  IllegalRun run = RunIllegal(
      "covergroup ucg (ref bit [1:0] v);\n"
      "  pu: coverpoint v { bins b[] = {[0:3]}; illegal_bins bad = {2}; }\n"
      "endgroup\n"
      "package pk;\n"
      "  covergroup pcg (ref bit [1:0] v);\n"
      "    pp: coverpoint v { bins b[] = {[0:3]}; illegal_bins bad = {2}; }\n"
      "  endgroup\n"
      "endpackage\n"
      "interface ifc;\n"
      "  bit [1:0] v;\n"
      "  covergroup icg;\n"
      "    pi: coverpoint v { bins b[] = {[0:3]}; illegal_bins bad = {2}; }\n"
      "  endgroup\n"
      "  icg c = new;\n"
      "  initial #1 begin v = 3; c.sample(); v = 2; c.sample(); end\n"
      "endinterface\n"
      "program pg;\n"
      "  bit [1:0] v;\n"
      "  covergroup gcg;\n"
      "    pg: coverpoint v { bins b[] = {[0:3]}; illegal_bins bad = {2}; }\n"
      "  endgroup\n"
      "  gcg c = new;\n"
      "  initial #9 begin v = 3; c.sample(); v = 2; c.sample(); end\n"
      "endprogram\n"
      "module top;\n"
      "  class K;\n"
      "    bit [1:0] w;\n"
      "    covergroup kcg;\n"
      "      pk: coverpoint w { bins b[] = {[0:3]}; illegal_bins bad = {2}; }\n"
      "    endgroup\n"
      "    function new(); kcg = new; endfunction\n"
      "  endclass\n"
      "  bit [1:0] v;\n"
      "  ifc i();\n"
      "  pg g();\n"
      "  pk::pcg p = new(v);\n"
      "  ucg u = new(v);\n"
      "  if (1) begin : gen\n"
      "    bit [1:0] x;\n"
      "    covergroup bcg;\n"
      "      bit [1:0] pb: coverpoint x { bins b[] = {[0:3]}; illegal_bins bad "
      "= {2}; }\n"
      "    endgroup\n"
      "    bcg c = new;\n"
      "    initial #3 begin x = 3; c.sample(); x = 2; c.sample(); end\n"
      "  end\n"
      "  initial begin\n"
      "    automatic K k = new;\n"
      "    #4 k.w = 3; k.kcg.sample(); k.w = 2; k.kcg.sample();\n"
      "    v = 3; p.sample(); u.sample();\n"
      "    v = 2; p.sample();\n"
      "    u.sample();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportsValueAt(run, "pi", 2, 15));
  EXPECT_TRUE(ReportsValueAt(run, "pg", 2, 23));
  EXPECT_TRUE(ReportsValueAt(run, "pb", 2, 44));
  EXPECT_TRUE(ReportsValueAt(run, "pk", 2, 48));
  EXPECT_TRUE(ReportsValueAt(run, "pp", 2, 50));
  EXPECT_TRUE(ReportsValueAt(run, "pu", 2, 51));
  EXPECT_EQ(run.errors, 6u);
}

}  // namespace
