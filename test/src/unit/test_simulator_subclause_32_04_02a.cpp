#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "parser/ast_specify.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

bool BuildTimingChecksFromSource(const std::string& src, SimFixture& f,
                                 SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  RegisterTimingChecks(*cu->modules.back(), f, mgr);
  return true;
}

void Annotate(const std::string& sdf, SpecifyManager& mgr) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

std::string SdfWith(const std::string& entry) {
  return "(DELAYFILE (CELL (CELLTYPE \"ff\") (INSTANCE u1) (TIMINGCHECK " +
         entry + ")))";
}

const char* const kDesign =
    "module t(input d, input clk, input clk2, input rst);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setup(d, posedge clk, 11, ntf);\n"
    "    $hold(posedge clk, d, 12, ntf);\n"
    "    $setuphold(posedge clk, d, 13, 14, ntf);\n"
    "    $recovery(posedge clk, rst, 15, ntf);\n"
    "    $removal(posedge clk, rst, 16, ntf);\n"
    "    $recrem(posedge clk, rst, 17, 18, ntf);\n"
    "    $skew(posedge clk, posedge clk2, 19, ntf);\n"
    "    $timeskew(posedge clk, posedge clk2, 20, ntf);\n"
    "    $fullskew(posedge clk, posedge clk2, 21, 22, ntf);\n"
    "    $width(posedge clk, 23, 5, ntf);\n"
    "    $period(posedge clk, 24, ntf);\n"
    "    $nochange(posedge clk, d, 25, 26, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

const TimingCheckEntry* Check(const SpecifyManager& mgr, TimingCheckKind kind) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind) return &tc;
  }
  return nullptr;
}

struct SdfTimingCheckMapping : public ::testing::Test {
  SimFixture f;
  SpecifyManager mgr;

  void SetUp() override {
    ASSERT_TRUE(BuildTimingChecksFromSource(kDesign, f, mgr));
    ASSERT_EQ(mgr.TimingCheckCount(), 12u);
  }

  void Run(const std::string& entry) { Annotate(SdfWith(entry), mgr); }

  uint64_t Limit(TimingCheckKind kind) {
    const auto* tc = Check(mgr, kind);
    return tc == nullptr ? 0u : tc->limit;
  }
  uint64_t Limit2(TimingCheckKind kind) {
    const auto* tc = Check(mgr, kind);
    return tc == nullptr ? 0u : tc->limit2;
  }
  uint64_t Threshold(TimingCheckKind kind) {
    const auto* tc = Check(mgr, kind);
    return tc == nullptr ? 0u : tc->threshold;
  }
};

TEST_F(SdfTimingCheckMapping, SetupReachesSetupAndTheSetupValueOfSetuphold) {
  Run("(SETUP d (posedge clk) (50))");

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 50u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 50u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 14u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 12u);
}

TEST_F(SdfTimingCheckMapping, HoldReachesHoldAndTheHoldValueOfSetuphold) {
  Run("(HOLD d (posedge clk) (60))");

  EXPECT_EQ(Limit(TimingCheckKind::kHold), 60u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 13u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 60u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 11u);
}

TEST_F(SdfTimingCheckMapping, EmptyValueHoldsWhatItStandsFor) {
  Run("(SETUPHOLD d (posedge clk) () (80)) (RECOVERY (posedge clk) rst (55))");

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 11u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 80u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 13u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 80u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecovery), 55u);
}

TEST(SdfTimingCheckSelect, BitSelectNamesTheCheckOnThatBit) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildTimingChecksFromSource("module t(input [1:0] d, input clk);\n"
                                  "  reg ntf;\n"
                                  "  specify\n"
                                  "    $setup(d[0], posedge clk, 1, ntf);\n"
                                  "  endspecify\n"
                                  "endmodule\n",
                                  f, mgr));

  Annotate(SdfWith("(SETUP d[1] (posedge clk) (7))"), mgr);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks().front().limit, 1u);

  Annotate(SdfWith("(SETUP d[0] (posedge clk) (5))"), mgr);
  EXPECT_EQ(mgr.GetTimingChecks().front().limit, 5u);
}

TEST(SdfTimingCheckConditionSignal, EachConditionMatchesOnItsOwnSignal) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildTimingChecksFromSource(
      "module t(input data, input clk, input mode, input en);\n"
      "  reg ntf;\n"
      "  specify\n"
      "    $setuphold(posedge clk &&& en, data &&& mode, 1, 1, ntf);\n"
      "    $setuphold(posedge clk &&& mode, data, 2, 2, ntf);\n"
      "  endspecify\n"
      "endmodule\n",
      f, mgr));

  Annotate(SdfWith("(SETUPHOLD (COND mode data) (posedge clk) (5) (6))"), mgr);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 5u);
  EXPECT_EQ(mgr.GetTimingChecks()[1].limit, 2u);
}

TEST(SdfTimingCheckTransitionEdge, TransitionEdgeNamesTheDescriptorItIs) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildTimingChecksFromSource(
      "module t(input data, input clk);\n"
      "  reg ntf;\n"
      "  specify\n"
      "    $setuphold(negedge clk, data, 1, 1, ntf);\n"
      "    $setuphold(edge [01] clk, data, 2, 2, ntf);\n"
      "  endspecify\n"
      "endmodule\n",
      f, mgr));

  Annotate(SdfWith("(SETUPHOLD data (01 clk) (5) (6))"), mgr);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[1].limit, 5u);
}

TEST(SdfTimingCheckNegativeValues, NegativeValuesKeepTheirSign) {
  SimFixture f;
  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions(
      TimingCheckInvocationOptions{true, false});
  ASSERT_TRUE(
      BuildTimingChecksFromSource("module t(input d, input clk);\n"
                                  "  reg ntf;\n"
                                  "  specify\n"
                                  "    $setuphold(posedge clk, d, 3, 4, ntf);\n"
                                  "    $nochange(posedge clk, d, 1, 2, ntf);\n"
                                  "  endspecify\n"
                                  "endmodule\n",
                                  f, mgr));

  Annotate(SdfWith("(SETUPHOLD d (posedge clk) (-2) (5))"
                   " (NOCHANGE (posedge clk) d (-1) (2))"),
           mgr);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  const TimingCheckEntry& setuphold = mgr.GetTimingChecks()[0];
  EXPECT_EQ(setuphold.signed_limit, -2);
  EXPECT_TRUE(setuphold.negative_timing_check_enabled);
  EXPECT_EQ(mgr.GetTimingChecks()[1].start_edge_offset, -1);
}

TEST(SdfTimingCheckTransitionEdge, EveryTransitionEdgeNamesItsDescriptor) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildTimingChecksFromSource(
      "module t(input data, input clk);\n"
      "  reg ntf;\n"
      "  specify\n"
      "    $setuphold(edge [10] clk, data, 1, 1, ntf);\n"
      "    $setuphold(edge [0x] clk, data, 1, 1, ntf);\n"
      "    $setuphold(edge [1x] clk, data, 1, 1, ntf);\n"
      "    $setuphold(edge [x0] clk, data, 1, 1, ntf);\n"
      "    $setuphold(edge [x1] clk, data, 1, 1, ntf);\n"
      "  endspecify\n"
      "endmodule\n",
      f, mgr));

  Annotate(SdfWith("(SETUPHOLD data (10 clk) (10) (6))"
                   " (SETUPHOLD data (0z clk) (20) (6))"
                   " (SETUPHOLD data (1z clk) (30) (6))"
                   " (SETUPHOLD data (z0 clk) (40) (6))"
                   " (SETUPHOLD data (z1 clk) (50) (6))"),
           mgr);
  ASSERT_EQ(mgr.TimingCheckCount(), 5u);
  for (std::size_t i = 0; i < 5; ++i) {
    EXPECT_EQ(mgr.GetTimingChecks()[i].limit, 10 * (i + 1)) << "check " << i;
  }
}

TEST_F(SdfTimingCheckMapping, SetupholdReachesSetupHoldAndSetuphold) {
  Run("(SETUPHOLD d (posedge clk) (70) (80))");

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 70u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 80u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 70u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 80u);

  const auto* nc = Check(mgr, TimingCheckKind::kNochange);
  ASSERT_NE(nc, nullptr);
  EXPECT_EQ(nc->start_edge_offset, 25);
  EXPECT_EQ(nc->end_edge_offset, 26);
}

TEST_F(SdfTimingCheckMapping,
       RecoveryReachesRecoveryAndTheRecoveryValueOfRecrem) {
  Run("(RECOVERY (posedge clk) rst (55))");

  EXPECT_EQ(Limit(TimingCheckKind::kRecovery), 55u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecrem), 55u);
  EXPECT_EQ(Limit2(TimingCheckKind::kRecrem), 18u);
  EXPECT_EQ(Limit(TimingCheckKind::kRemoval), 16u);
}

TEST_F(SdfTimingCheckMapping, RemovalReachesRemovalAndTheRemovalValueOfRecrem) {
  Run("(REMOVAL (posedge clk) rst (65))");

  EXPECT_EQ(Limit(TimingCheckKind::kRemoval), 65u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecrem), 17u);
  EXPECT_EQ(Limit2(TimingCheckKind::kRecrem), 65u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecovery), 15u);
}

TEST_F(SdfTimingCheckMapping, RecremReachesRecoveryRemovalAndRecrem) {
  Run("(RECREM (posedge clk) rst (75) (85))");

  EXPECT_EQ(Limit(TimingCheckKind::kRecovery), 75u);
  EXPECT_EQ(Limit(TimingCheckKind::kRemoval), 85u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecrem), 75u);
  EXPECT_EQ(Limit2(TimingCheckKind::kRecrem), 85u);
}

TEST_F(SdfTimingCheckMapping, SkewReachesSkewAndTimeskew) {
  Run("(SKEW (posedge clk) (posedge clk2) (90))");

  EXPECT_EQ(Limit(TimingCheckKind::kSkew), 90u);
  EXPECT_EQ(Limit(TimingCheckKind::kTimeskew), 90u);
  EXPECT_EQ(Limit(TimingCheckKind::kFullskew), 21u);
  EXPECT_EQ(Limit2(TimingCheckKind::kFullskew), 22u);
}

TEST_F(SdfTimingCheckMapping, BidirectskewReachesOnlyFullskew) {
  Run("(BIDIRECTSKEW (posedge clk) (posedge clk2) (91) (92))");

  EXPECT_EQ(Limit(TimingCheckKind::kFullskew), 91u);
  EXPECT_EQ(Limit2(TimingCheckKind::kFullskew), 92u);
  EXPECT_EQ(Limit(TimingCheckKind::kSkew), 19u);
  EXPECT_EQ(Limit(TimingCheckKind::kTimeskew), 20u);
}

TEST_F(SdfTimingCheckMapping, WidthReachesWidthLimitButNotItsSecondValue) {
  Run("(WIDTH (posedge clk) (93))");

  EXPECT_EQ(Limit(TimingCheckKind::kWidth), 93u);
  EXPECT_EQ(Threshold(TimingCheckKind::kWidth), 5u);
  EXPECT_EQ(Limit2(TimingCheckKind::kWidth), 0u);
  EXPECT_EQ(Limit(TimingCheckKind::kPeriod), 24u);
}

TEST_F(SdfTimingCheckMapping, PeriodReachesOnlyPeriod) {
  Run("(PERIOD (posedge clk) (94))");

  EXPECT_EQ(Limit(TimingCheckKind::kPeriod), 94u);
  EXPECT_EQ(Limit(TimingCheckKind::kWidth), 23u);
}

TEST_F(SdfTimingCheckMapping, NochangeReachesNochangeEdgeOffsets) {
  Run("(NOCHANGE (posedge clk) d (7) (8))");

  const auto* nc = Check(mgr, TimingCheckKind::kNochange);
  ASSERT_NE(nc, nullptr);
  EXPECT_EQ(nc->start_edge_offset, 7);
  EXPECT_EQ(nc->end_edge_offset, 8);

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 11u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 12u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 13u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 14u);
}

TEST_F(SdfTimingCheckMapping, CheckOnAnUndeclaredSignalReachesNothing) {
  Run("(SETUP d (posedge nosuchclk) (99))");

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 11u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 12u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 13u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 14u);
}

TEST_F(SdfTimingCheckMapping, AnnotatedSkewLimitIsTheOneTheCheckRunsOn) {
  EXPECT_TRUE(mgr.CheckSkewViolation("clk", 100, "clk2", 150));

  Run("(SKEW (posedge clk) (posedge clk2) (90))");

  EXPECT_FALSE(mgr.CheckSkewViolation("clk", 100, "clk2", 150));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk", 100, "clk2", 200));
}

TEST_F(SdfTimingCheckMapping, SetupholdValuesReachTheSlotsTheyRunOn) {
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "d", 25));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "d", 175));

  Run("(SETUPHOLD d (posedge clk) (70) (80))");

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "d", 25));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "d", 175));
}

const char* const kConditionedDesign =
    "module t(input data, input clk, input mode);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(posedge clk &&& mode, data, 1, 1, ntf);\n"
    "    $setuphold(negedge clk &&& !mode, data, 2, 2, ntf);\n"
    "    $setuphold(edge clk, data, 3, 3, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kDataConditionedDesign =
    "module t(input data, input clk, input mode);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(posedge clk, data &&& mode, 1, 1, ntf);\n"
    "    $setuphold(posedge clk, data &&& !mode, 2, 2, ntf);\n"
    "    $setuphold(posedge clk, data, 3, 3, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

struct SdfTimingCheckConditionMatching : public ::testing::Test {
  SimFixture f;
  SpecifyManager mgr;

  void Build(const char* design) {
    ASSERT_TRUE(BuildTimingChecksFromSource(design, f, mgr));
    ASSERT_EQ(mgr.TimingCheckCount(), 3u);
  }

  void Run(const std::string& entry) { Annotate(SdfWith(entry), mgr); }

  const TimingCheckEntry* Declared(SpecifyEdge ref_edge,
                                   std::string_view condition) {
    for (const auto& tc : mgr.GetTimingChecks()) {
      if (tc.ref_edge == ref_edge && tc.condition == condition) return &tc;
    }
    return nullptr;
  }

  void ExpectLimits(const TimingCheckEntry* tc, uint64_t limit,
                    uint64_t limit2) {
    ASSERT_NE(tc, nullptr);
    EXPECT_EQ(tc->limit, limit);
    EXPECT_EQ(tc->limit2, limit2);
  }
};

TEST_F(SdfTimingCheckConditionMatching,
       BareCheckReachesEveryCorrespondingDeclaration) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data clk (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 5, 6);
}

TEST_F(SdfTimingCheckConditionMatching,
       EdgeOnTheSdfCheckMustMatchBeforeAnnotation) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (posedge clk) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 2, 2);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

TEST_F(SdfTimingCheckConditionMatching, ConditionAndEdgeTogetherMustBothMatch) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (COND !mode (posedge clk)) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 1, 1);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 2, 2);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

TEST_F(SdfTimingCheckConditionMatching,
       ConditionAndEdgeTogetherAnnotateTheDeclarationCarryingBoth) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (COND mode (posedge clk)) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 2, 2);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

TEST_F(SdfTimingCheckConditionMatching,
       ConditionOnTheReferenceSignalMustMatch) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (COND !mode clk) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 1, 1);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

TEST_F(SdfTimingCheckConditionMatching, ConditionOnTheDataSignalMustMatch) {
  Build(kDataConditionedDesign);
  Run("(SETUPHOLD (COND !mode data) clk (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 1, 1);
  ExpectLimits(Declared(SpecifyEdge::kPosedge, "!mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kPosedge, ""), 3, 3);
}

const char* const kDataEdgeDesign =
    "module t(input data, input clk);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(posedge clk, posedge data, 1, 1, ntf);\n"
    "    $setuphold(posedge clk, negedge data, 2, 2, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

TEST(SdfTimingCheckDataEdge, EdgeOnTheDataSignalMustMatchBeforeAnnotation) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildTimingChecksFromSource(kDataEdgeDesign, f, mgr));
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);

  Annotate(SdfWith("(SETUPHOLD (posedge data) clk (5) (6))"), mgr);

  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.data_edge == SpecifyEdge::kPosedge) {
      EXPECT_EQ(tc.limit, 5u);
      EXPECT_EQ(tc.limit2, 6u);
    } else {
      EXPECT_EQ(tc.data_edge, SpecifyEdge::kNegedge);
      EXPECT_EQ(tc.limit, 2u);
      EXPECT_EQ(tc.limit2, 2u);
    }
  }
}

const char* const kNoEdgeDesign =
    "module t(input data, input clk);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(clk, data, 1, 1, ntf);\n"
    "    $setuphold(posedge clk, data, 2, 2, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

TEST(SdfTimingCheckEdgelessDeclaration, IsNotMatchedByAnSdfReferenceEdge) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildTimingChecksFromSource(kNoEdgeDesign, f, mgr));
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);

  Annotate(SdfWith("(SETUPHOLD data (posedge clk) (5) (6))"), mgr);

  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.ref_edge == SpecifyEdge::kPosedge) {
      EXPECT_EQ(tc.limit, 5u);
      EXPECT_EQ(tc.limit2, 6u);
    } else {
      EXPECT_EQ(tc.ref_edge, SpecifyEdge::kNone);
      EXPECT_EQ(tc.limit, 1u);
      EXPECT_EQ(tc.limit2, 1u);
    }
  }
}

TEST(SdfTimingCheckEdgelessDeclaration, IsNotMatchedByAnSdfDataEdge) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildTimingChecksFromSource(kNoEdgeDesign, f, mgr));
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);

  Annotate(SdfWith("(SETUPHOLD (posedge data) clk (5) (6))"), mgr);

  for (const auto& tc : mgr.GetTimingChecks()) {
    EXPECT_EQ(tc.data_edge, SpecifyEdge::kNone);
    if (tc.ref_edge == SpecifyEdge::kPosedge) {
      EXPECT_EQ(tc.limit, 2u);
      EXPECT_EQ(tc.limit2, 2u);
    } else {
      EXPECT_EQ(tc.limit, 1u);
      EXPECT_EQ(tc.limit2, 1u);
    }
  }
}

const char* const kBothEdgeDesign =
    "module t(input data, input clk);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(posedge clk, posedge data, 1, 1, ntf);\n"
    "    $setuphold(posedge clk, negedge data, 2, 2, ntf);\n"
    "    $setuphold(negedge clk, posedge data, 3, 3, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

TEST(SdfTimingCheckBothSignalEdges, EveryEdgeNamedMustMatchBeforeAnnotation) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildTimingChecksFromSource(kBothEdgeDesign, f, mgr));
  ASSERT_EQ(mgr.TimingCheckCount(), 3u);

  Annotate(SdfWith("(SETUPHOLD (posedge data) (posedge clk) (5) (6))"), mgr);

  for (const auto& tc : mgr.GetTimingChecks()) {
    const bool kRefMatches = tc.ref_edge == SpecifyEdge::kPosedge;
    const bool kDataMatches = tc.data_edge == SpecifyEdge::kPosedge;
    if (kRefMatches && kDataMatches) {
      EXPECT_EQ(tc.limit, 5u);
      EXPECT_EQ(tc.limit2, 6u);
    } else if (kRefMatches) {
      EXPECT_EQ(tc.limit, 2u);
      EXPECT_EQ(tc.limit2, 2u);
    } else {
      EXPECT_EQ(tc.limit, 3u);
      EXPECT_EQ(tc.limit2, 3u);
    }
  }
}

SpecifyManager* ManagerAfterRun(const std::string& source, SimFixture& f) {
  auto* design = ElaborateSrc(source, f);
  if (design == nullptr || f.has_errors) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.GetSpecifyManager();
}

void AnnotateUnderDesignRoot(const std::string& sdf, SpecifyManager& mgr,
                             std::string_view design_root) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, {}, design_root);
}

std::string SetupRecord(const std::string& cell_type,
                        const std::string& instance, const std::string& limit) {
  return "  (CELL (CELLTYPE \"" + cell_type + "\") (INSTANCE " + instance +
         ") (TIMINGCHECK (SETUP d (posedge clk) (" + limit + "))))\n";
}

std::string DelayFileOf(const std::string& records) {
  return "(DELAYFILE\n" + records + ")\n";
}

uint64_t SetupLimitIn(const SpecifyManager& mgr, std::string_view prefix) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == TimingCheckKind::kSetup && tc.inst_prefix == prefix) {
      return tc.limit;
    }
  }
  ADD_FAILURE() << "no $setup was registered under the instance prefix '"
                << prefix << "'";
  return 0;
}

const char* const kTwoInstanceDesign =
    "module annotated_cell(input d, input clk, output q);\n"
    "  specify\n"
    "    $setup(d, posedge clk, 31);\n"
    "  endspecify\n"
    "endmodule\n"
    "module top;\n"
    "  logic first_q;\n"
    "  logic second_q;\n"
    "  annotated_cell u_first(1'b0, 1'b0, first_q);\n"
    "  annotated_cell u_second(1'b0, 1'b0, second_q);\n"
    "endmodule\n";

TEST(SdfTimingCheckInstanceScope,
     EachInstanceTakesTheLimitOfTheRecordNamingIt) {
  SimFixture f;
  SpecifyManager* mgr = ManagerAfterRun(kTwoInstanceDesign, f);
  ASSERT_NE(mgr, nullptr);
  ASSERT_EQ(mgr->TimingCheckCount(), 2u);

  AnnotateUnderDesignRoot(
      DelayFileOf(SetupRecord("annotated_cell", "top/u_first", "41") +
                  SetupRecord("annotated_cell", "top/u_second", "59")),
      *mgr, "top");

  EXPECT_EQ(SetupLimitIn(*mgr, "u_first."), 41u);
  EXPECT_EQ(SetupLimitIn(*mgr, "u_second."), 59u);
}

TEST(SdfTimingCheckInstanceScope,
     ARecordNamingOneInstanceLeavesTheOtherAsDeclared) {
  SimFixture f;
  SpecifyManager* mgr = ManagerAfterRun(kTwoInstanceDesign, f);
  ASSERT_NE(mgr, nullptr);
  ASSERT_EQ(mgr->TimingCheckCount(), 2u);

  AnnotateUnderDesignRoot(
      DelayFileOf(SetupRecord("annotated_cell", "top/u_second", "67")), *mgr,
      "top");

  EXPECT_EQ(SetupLimitIn(*mgr, "u_second."), 67u);
  EXPECT_EQ(SetupLimitIn(*mgr, "u_first."), 31u);
}

const char* const kRootAndInstanceDesign =
    "module rooted_cell(input d, input clk, output q);\n"
    "  specify\n"
    "    $setup(d, posedge clk, 37);\n"
    "  endspecify\n"
    "endmodule\n"
    "module top(\n"
    "    output logic d,\n"
    "    output logic clk);\n"
    "  logic inner_q;\n"
    "  rooted_cell u_inner(1'b0, 1'b0, inner_q);\n"
    "  specify\n"
    "    $setup(d, posedge clk, 23);\n"
    "  endspecify\n"
    "endmodule\n";

TEST(SdfTimingCheckInstanceScope,
     ARecordNamingTheDesignRootReachesTheTopsOwnCheck) {
  SimFixture f;
  SpecifyManager* mgr = ManagerAfterRun(kRootAndInstanceDesign, f);
  ASSERT_NE(mgr, nullptr);
  ASSERT_EQ(mgr->TimingCheckCount(), 2u);

  AnnotateUnderDesignRoot(DelayFileOf(SetupRecord("top", "top", "83")), *mgr,
                          "top");

  EXPECT_EQ(SetupLimitIn(*mgr, ""), 83u);
  EXPECT_EQ(SetupLimitIn(*mgr, "u_inner."), 37u);
}

const TimingCheckEntry* NegativeCheckAnnotated(const std::string& values,
                                               SimFixture& f) {
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions(
      TimingCheckInvocationOptions{true, false});
  SpecifyManager* mgr = ManagerAfterRun(
      "module top(input clk, input d);\n  specify\n"
      "    $setuphold(posedge clk, d, -10, 20);\n  endspecify\nendmodule\n",
      f);
  if (mgr == nullptr || mgr->TimingCheckCount() != 1) return nullptr;
  AnnotateUnderDesignRoot(
      DelayFileOf("  (CELL (CELLTYPE \"top\") (INSTANCE top) (TIMINGCHECK "
                  "(SETUPHOLD d (posedge clk) " +
                  values + ")))\n"),
      *mgr, "top");
  return &mgr->GetTimingChecks().front();
}

TEST(SdfTimingCheckNegativeLimits, AnnotationReachesTheSignedLimits) {
  SimFixture f;
  const TimingCheckEntry* check = NegativeCheckAnnotated("(-5) (6)", f);
  ASSERT_NE(check, nullptr);
  EXPECT_TRUE(check->negative_timing_check_enabled);
  EXPECT_EQ(check->signed_limit, -5);
  EXPECT_EQ(check->signed_limit2, 6);
}

TEST(SdfTimingCheckNegativeLimits, NonNegativeValuesEndNegativeHandling) {
  SimFixture f;
  const TimingCheckEntry* check = NegativeCheckAnnotated("(3) ()", f);
  ASSERT_NE(check, nullptr);
  SpecifyManager& mgr = f.ctx.AcquireSpecifyManager();
  const int64_t kShift =
      static_cast<int64_t>(mgr.TimingCheckSignalDelay("clk")) -
      static_cast<int64_t>(mgr.TimingCheckSignalDelay("d"));
  ASSERT_GT(kShift, 0);
  EXPECT_FALSE(check->negative_timing_check_enabled);
  EXPECT_EQ(check->signed_limit, 3 + kShift);
  EXPECT_EQ(check->signed_limit2, 20 - kShift);
}

}  // namespace
