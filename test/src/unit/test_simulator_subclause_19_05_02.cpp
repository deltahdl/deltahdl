#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(CoverageTransitionBins, TransitionBinRejectedForRealCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* integral = CoverageDB::AddCoverPoint(g, "v");
  auto* real_cp = CoverageDB::AddCoverPoint(g, "r");
  real_cp->is_real = true;

  EXPECT_TRUE(CoverageDB::TransitionBinAllowed(integral));
  EXPECT_FALSE(CoverageDB::TransitionBinAllowed(real_cp));
}

TEST(CoverageTransitionBins, LengthZeroTransitionIllegal) {
  EXPECT_FALSE(CoverageDB::TransitionLengthLegal(0));
  EXPECT_FALSE(CoverageDB::TransitionLengthLegal(1));
  EXPECT_TRUE(CoverageDB::TransitionLengthLegal(2));
  EXPECT_TRUE(CoverageDB::TransitionLengthLegal(5));
}

TEST(CoverageTransitionBins, SetTransitionExpandsToProduct) {
  auto seqs = CoverageDB::ExpandSetTransition({{1, 5}, {6, 7}});
  ASSERT_EQ(seqs.size(), 4u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{1, 6}));
  EXPECT_EQ(seqs[1], (std::vector<int64_t>{1, 7}));
  EXPECT_EQ(seqs[2], (std::vector<int64_t>{5, 6}));
  EXPECT_EQ(seqs[3], (std::vector<int64_t>{5, 7}));
}

TEST(CoverageTransitionBins, SetTransitionThreeSteps) {
  auto seqs = CoverageDB::ExpandSetTransition({{1}, {3}, {5}});
  ASSERT_EQ(seqs.size(), 1u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{1, 3, 5}));
}

TEST(CoverageTransitionBins, ConsecutiveRepeatFixedCount) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({3}, 5, 5);
  ASSERT_EQ(seqs.size(), 1u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{3, 3, 3, 3, 3}));
}

TEST(CoverageTransitionBins, ConsecutiveRepeatRange) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({3}, 3, 5);
  ASSERT_EQ(seqs.size(), 3u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{3, 3, 3}));
  EXPECT_EQ(seqs[1], (std::vector<int64_t>{3, 3, 3, 3}));
  EXPECT_EQ(seqs[2], (std::vector<int64_t>{3, 3, 3, 3, 3}));
}

TEST(CoverageTransitionBins, ArrayBinNamesEmbedTransition) {
  EXPECT_EQ(CoverageDB::TransitionArrayBinName("sb", {4, 5, 6}), "sb[4=>5=>6]");
  EXPECT_EQ(CoverageDB::TransitionArrayBinName("sb", {10, 12}), "sb[10=>12]");
}

TEST(CoverageTransitionBins, UnboundedRepeatRejectedForMultipleBins) {
  EXPECT_TRUE(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kConsecutive));
  EXPECT_FALSE(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kGoto));
  EXPECT_FALSE(CoverageDB::TransitionRepeatBounded(
      TransitionRepeatKind::kNonconsecutive));

  EXPECT_TRUE(CoverageDB::MultipleBinsAllowsTransition(true));
  EXPECT_FALSE(CoverageDB::MultipleBinsAllowsTransition(false));
}

TEST(CoverageTransitionBins, DefaultSequenceRejectsMultipleBins) {
  EXPECT_FALSE(CoverageDB::DefaultSequenceAllowsMultipleBins());
}

TEST(CoverageTransitionBins, DefaultSequenceIncrementCondition) {
  EXPECT_TRUE(CoverageDB::DefaultSequenceTransitionIncrements(false, false));
  EXPECT_FALSE(CoverageDB::DefaultSequenceTransitionIncrements(true, false));
  EXPECT_FALSE(CoverageDB::DefaultSequenceTransitionIncrements(false, true));
}

TEST(CoverageTransitionBins, TransitionBinCountsAtMostOncePerSample) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "t";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = {{1, 2}, {1, 2}};
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 2}});
  EXPECT_EQ(b->hit_count, 1u);

  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 2}});
  EXPECT_EQ(b->hit_count, 2u);
}

TEST(CoverageTransitionBins, SetTransitionWithNoStepsYieldsNothing) {
  auto seqs = CoverageDB::ExpandSetTransition({});
  EXPECT_TRUE(seqs.empty());
}

TEST(CoverageTransitionBins, ConsecutiveRepeatInvertedRangeYieldsNothing) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({3}, 5, 3);
  EXPECT_TRUE(seqs.empty());
}

TEST(CoverageTransitionBins, MultiStepSequenceIncrementsWhenCompleted) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "s";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = {{1, 3, 4, 5}};
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 3}});
  db.Sample(g, {{"v", 9}});
  EXPECT_EQ(b->hit_count, 0u);

  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 3}});
  db.Sample(g, {{"v", 4}});
  EXPECT_EQ(b->hit_count, 0u);
  db.Sample(g, {{"v", 5}});
  EXPECT_EQ(b->hit_count, 1u);
}

TEST(CoverageTransitionBins, OverlappingConsecutiveMatchesEachIncrement) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "b5";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = CoverageDB::ExpandConsecutiveRepeat({5}, 3, 3);
  ASSERT_EQ(bin.transitions.size(), 1u);
  ASSERT_EQ(bin.transitions[0], (std::vector<int64_t>{5, 5, 5}));
  auto* b = CoverageDB::AddBin(cp, bin);

  for (int i = 0; i < 6; ++i) db.Sample(g, {{"v", 5}});
  EXPECT_EQ(b->hit_count, 4u);
}

TEST(CoverageTransitionBins, SetTransitionProductDrivesSingleBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "sa";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = CoverageDB::ExpandSetTransition({{1, 5}, {6, 7}});
  ASSERT_EQ(bin.transitions.size(), 4u);
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 6}});
  EXPECT_EQ(b->hit_count, 1u);
  db.Sample(g, {{"v", 5}});
  db.Sample(g, {{"v", 7}});
  EXPECT_EQ(b->hit_count, 2u);
}

TEST(CoverageTransitionBins, ArrayElementBinsTrackOwnTransition) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");

  auto expanded = CoverageDB::ExpandSetTransition({{1, 5}, {6, 7}});
  std::vector<CoverBin*> elems;
  for (const auto& seq : expanded) {
    CoverBin bin;
    bin.name = CoverageDB::TransitionArrayBinName("sb", seq);
    bin.kind = CoverBinKind::kTransition;
    bin.transitions = {seq};
    elems.push_back(CoverageDB::AddBin(cp, bin));
  }
  ASSERT_EQ(elems.size(), 4u);
  EXPECT_EQ(elems[0]->name, "sb[1=>6]");
  EXPECT_EQ(elems[3]->name, "sb[5=>7]");

  db.Sample(g, {{"v", 5}});
  db.Sample(g, {{"v", 7}});
  EXPECT_EQ(elems[0]->hit_count, 0u);
  EXPECT_EQ(elems[1]->hit_count, 0u);
  EXPECT_EQ(elems[2]->hit_count, 0u);
  EXPECT_EQ(elems[3]->hit_count, 1u);
}

TEST(CoverageTransitionBins, RepeatOnceProducesIllegalLengthZeroSpec) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({0}, 1, 1);
  ASSERT_EQ(seqs.size(), 1u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{0}));
  EXPECT_FALSE(CoverageDB::TransitionLengthLegal(seqs[0].size()));
}

TEST(CoverageTransitionBins, SetTransitionRangeStepExpandsToProduct) {
  auto seqs = CoverageDB::ExpandSetTransition({{7, 8, 9, 10}, {11, 12}});
  ASSERT_EQ(seqs.size(), 8u);
  EXPECT_EQ(seqs.front(), (std::vector<int64_t>{7, 11}));
  EXPECT_EQ(seqs.back(), (std::vector<int64_t>{10, 12}));

  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "sa2";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = seqs;
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 9}});
  db.Sample(g, {{"v", 11}});
  EXPECT_EQ(b->hit_count, 1u);
  db.Sample(g, {{"v", 10}});
  db.Sample(g, {{"v", 12}});
  EXPECT_EQ(b->hit_count, 2u);
}

TEST(CoverageTransitionBins, MultiSetTransListFeedsSingleBin) {
  auto set1 = CoverageDB::ExpandSetTransition({{4}, {5}, {6}});
  auto set2 = CoverageDB::ExpandSetTransition({{7, 8, 9, 10}, {11, 12}});
  ASSERT_EQ(set1.size(), 1u);
  ASSERT_EQ(set2.size(), 8u);

  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "sa";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = set1;
  bin.transitions.insert(bin.transitions.end(), set2.begin(), set2.end());
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 4}});
  db.Sample(g, {{"v", 5}});
  db.Sample(g, {{"v", 6}});
  EXPECT_EQ(b->hit_count, 1u);

  db.Sample(g, {{"v", 8}});
  db.Sample(g, {{"v", 12}});
  EXPECT_EQ(b->hit_count, 2u);
}

TEST(CoverageTransitionBins, SingleRangeTransitionSpecIsIllegalLengthZero) {
  auto seqs = CoverageDB::ExpandSetTransition({{0, 1}});
  ASSERT_EQ(seqs.size(), 2u);
  for (const auto& seq : seqs) {
    EXPECT_EQ(seq.size(), 1u);
    EXPECT_FALSE(CoverageDB::TransitionLengthLegal(seq.size()));
  }
}

TEST(CoverageTransitionBins, RangeRepeatedOnceIsIllegalLengthZero) {
  for (int64_t value : {int64_t{0}, int64_t{1}}) {
    auto seqs = CoverageDB::ExpandConsecutiveRepeat({value}, 1, 1);
    ASSERT_EQ(seqs.size(), 1u);
    EXPECT_EQ(seqs[0], (std::vector<int64_t>{value}));
    EXPECT_FALSE(CoverageDB::TransitionLengthLegal(seqs[0].size()));
  }
}

static TransitionPatternElement PatValue(int64_t value) {
  TransitionPatternElement e;
  e.values = {value};
  e.has_repeat = false;
  return e;
}

static TransitionPatternElement PatRepeat(int64_t value, TransitionRepeatKind k,
                                          uint32_t lo, uint32_t hi) {
  TransitionPatternElement e;
  e.values = {value};
  e.has_repeat = true;
  e.repeat_kind = k;
  e.repeat_lo = lo;
  e.repeat_hi = hi;
  return e;
}

TEST(CoverageTransitionBins, GotoRepetitionMatchesAcrossInterveningSamples) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "t";
  bin.kind = CoverBinKind::kTransition;
  bin.transition_patterns = {{PatRepeat(3, TransitionRepeatKind::kGoto, 2, 2)}};
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 3}});
  EXPECT_EQ(b->hit_count, 0u);
  db.Sample(g, {{"v", 7}});
  db.Sample(g, {{"v", 4}});
  EXPECT_EQ(b->hit_count, 0u);
  db.Sample(g, {{"v", 3}});
  EXPECT_EQ(b->hit_count, 1u);
}

TEST(CoverageTransitionBins,
     GotoRequiresImmediateFollowNonconsecutiveTolerates) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* goto_cp = CoverageDB::AddCoverPoint(g, "vg");
  CoverBin goto_bin;
  goto_bin.name = "g";
  goto_bin.kind = CoverBinKind::kTransition;
  goto_bin.transition_patterns = {
      {PatRepeat(2, TransitionRepeatKind::kGoto, 2, 2), PatValue(5)}};
  auto* gb = CoverageDB::AddBin(goto_cp, goto_bin);

  auto* nc_cp = CoverageDB::AddCoverPoint(g, "vn");
  CoverBin nc_bin;
  nc_bin.name = "n";
  nc_bin.kind = CoverBinKind::kTransition;
  nc_bin.transition_patterns = {
      {PatRepeat(2, TransitionRepeatKind::kNonconsecutive, 2, 2), PatValue(5)}};
  auto* nb = CoverageDB::AddBin(nc_cp, nc_bin);

  for (int64_t v : {int64_t{2}, int64_t{2}, int64_t{9}, int64_t{5}}) {
    db.Sample(g, {{"vg", v}, {"vn", v}});
  }
  EXPECT_EQ(gb->hit_count, 0u);
  EXPECT_EQ(nb->hit_count, 1u);
}

TEST(CoverageTransitionBins, WorkedExampleReproducesStandardBinCounts) {
  CoverageDB db;
  auto* g = db.CreateGroup("sg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");

  CoverBin b2;
  b2.name = "b2";
  b2.kind = CoverBinKind::kTransition;
  b2.transition_patterns = {{PatRepeat(2, TransitionRepeatKind::kGoto, 3, 5)}};
  auto* pb2 = CoverageDB::AddBin(cp, b2);

  CoverBin b3;
  b3.name = "b3";
  b3.kind = CoverBinKind::kTransition;
  b3.transition_patterns = {{PatRepeat(3, TransitionRepeatKind::kGoto, 3, 5)}};
  auto* pb3 = CoverageDB::AddBin(cp, b3);

  CoverBin b5;
  b5.name = "b5";
  b5.kind = CoverBinKind::kTransition;
  b5.transitions = CoverageDB::ExpandConsecutiveRepeat({5}, 3, 3);
  auto* pb5 = CoverageDB::AddBin(cp, b5);

  CoverBin b6;
  b6.name = "b6";
  b6.kind = CoverBinKind::kTransition;
  b6.transition_patterns = {{PatValue(1),
                             PatRepeat(3, TransitionRepeatKind::kGoto, 4, 6),
                             PatValue(1)}};
  auto* pb6 = CoverageDB::AddBin(cp, b6);

  CoverBin b7;
  b7.name = "b7";
  b7.kind = CoverBinKind::kTransition;
  b7.transition_patterns = {
      {PatValue(1), PatRepeat(2, TransitionRepeatKind::kNonconsecutive, 3, 6),
       PatValue(5)}};
  auto* pb7 = CoverageDB::AddBin(cp, b7);

  const std::vector<int64_t> kStream = {1, 4, 3, 2, 3, 3, 2, 2, 3,
                                        2, 3, 1, 5, 5, 5, 5, 5, 5};
  for (int64_t v : kStream) db.Sample(g, {{"v", v}});

  EXPECT_EQ(pb2->hit_count, 2u);
  EXPECT_EQ(pb3->hit_count, 3u);
  EXPECT_EQ(pb5->hit_count, 4u);
  EXPECT_EQ(pb6->hit_count, 1u);
  EXPECT_EQ(pb7->hit_count, 1u);
}

TEST(CovergroupInstanceSim, TransitionBinCountsItsSequence) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v; int n, t;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins t = (1 => 2); bins u = (2 => 3); }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    v = 1; c.sample(); v = 2; c.sample();\n"
                 "    void'(c.get_inst_coverage(n, t));\n"
                 "    $display(\"n=%0d t=%0d\", n, t);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, DefaultSequenceBinCountsTransitionsNoBinTakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [4:1] v_a; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v_a {\n"
                       "      bins sa = (4 => 5 => 6), ([7:9],10 => 11,12);\n"
                       "      bins sc = (12 => 3 [-> 1]);\n"
                       "      bins allother = default sequence;\n"
                       "    }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v_a = 4; c.sample(); v_a = 5; c.sample();\n"
                       "    v_a = 7; c.sample(); v_a = 11; c.sample();\n"
                       "    v_a = 8; c.sample(); v_a = 12; c.sample();\n"
                       "    v_a = 2; c.sample(); v_a = 2; c.sample();\n"
                       "    v_a = 3; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=2 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const CoverGroup* group = f.ctx.CoverageData().FindGroup("c");
  ASSERT_NE(group, nullptr);
  const CoverBin& allother = group->coverpoints[0].bins.back();
  EXPECT_EQ(allother.name, "allother");
  EXPECT_EQ(allother.hit_count, 2u);
}

TEST(CovergroupInstanceSim, DefaultSequenceBinIffGuardSuppressesItsCount) {
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  bit [1:0] v; bit en;\n"
      "  covergroup cg;\n"
      "    coverpoint v { bins t = (1 => 2); "
      "bins d = default sequence iff (en); }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    en = 1; v = 0; c.sample(); v = 3; c.sample();\n"
      "    en = 0; v = 0; c.sample();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const CoverGroup* group = f.ctx.CoverageData().FindGroup("c");
  ASSERT_NE(group, nullptr);
  EXPECT_EQ(group->coverpoints[0].bins[1].name, "d");
  EXPECT_EQ(group->coverpoints[0].bins[1].hit_count, 1u);
}

TEST(CovergroupInstanceSim, DefaultSequenceBinIsLeftOutOfACross) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v, w; int n, t;\n"
                       "  covergroup cg;\n"
                       "    a: coverpoint v { bins one = {1}; "
                       "bins d = default sequence; }\n"
                       "    b: coverpoint w { bins one = {1}; }\n"
                       "    X: cross a, b;\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin v = 1; w = 1; c.sample(); "
                       "void'(c.X.get_inst_coverage(n, t)); "
                       "$display(\"n=%0d t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
