#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.4.2 is entirely about which *declared* SystemVerilog timing check an SDF
// timing check lands on, so how each check was declared -- its type, its two
// signals, the edges (§31.5) and conditioned events (§31.7) on them -- is the
// whole subject. Every test below therefore builds its SystemVerilog side from
// real source: BuildTimingChecksFromSource parses, elaborates and runs a module
// and then registers the specify block's timing check declarations through the
// production builder. The SDF side is likewise real SDF text handed to
// ParseSdf. Nothing on either side is hand-assembled.
bool BuildTimingChecksFromSource(const std::string& src, SimFixture& f,
                                 SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  RegisterTimingChecks(*cu->modules.back(), f, mgr);
  return true;
}

// Annotates real SDF text onto a manager that was filled from real source.
void Annotate(const std::string& sdf, SpecifyManager& mgr) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

// Wraps a TIMINGCHECK section body in the enclosing DELAYFILE/CELL structure an
// SDF file always supplies, so each test only writes the entry under test.
std::string SdfWith(const std::string& entry) {
  return "(DELAYFILE (CELL (CELLTYPE \"ff\") (INSTANCE u1) (TIMINGCHECK " +
         entry + ")))";
}

// One declaration of every timing check Table 32-2 names a target for, so a
// construct that is supposed to reach one or two of them can be checked against
// the ones it must leave alone. Every declared limit is distinct, so untouched
// never reads as overwritten. The setup/hold/setuphold/nochange group shares
// the clk-d signal pair, the recovery/removal/recrem group shares clk-rst and
// the skew group shares clk-clk2, which is what makes "same names, other type"
// the thing the mapping has to get right. $setup writes its data event first
// (Syntax 31-3) where every other check here writes the reference event first,
// so its d precedes its posedge clk and it still names the clk-d pair.
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

// Locates the one declared check of a given type. Each type appears once in
// kDesign, so the type alone identifies it.
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
  // §31.4.4's threshold, which is where a declared $width's third argument
  // stands. It is not limit2: §31.4.4 gives $width one timing_check_limit, and
  // BuildTimingCheckUnderOptions (simulator/specify_timing_check.cpp) leaves
  // limit2 at zero for that kind.
  uint64_t Threshold(TimingCheckKind kind) {
    const auto* tc = Check(mgr, kind);
    return tc == nullptr ? 0u : tc->threshold;
  }
};

// Table 32-2 row 1: SETUP carries one value, which reaches $setup and the setup
// value of $setuphold. The x in the table's $setuphold(v1,x) is the hold value:
// SETUP says nothing about it, so it keeps what the declaration gave it. $hold
// is a different type and is not a target of this row at all.
TEST_F(SdfTimingCheckMapping, SetupReachesSetupAndTheSetupValueOfSetuphold) {
  Run("(SETUP d (posedge clk) (50))");

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 50u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 50u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 14u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 12u);
}

// Table 32-2 row 2: HOLD's single value reaches $hold and the *hold* value of
// $setuphold -- $setuphold(x,v1) -- leaving the setup value alone. $setup
// shares both signal names with $hold and is left alone too.
TEST_F(SdfTimingCheckMapping, HoldReachesHoldAndTheHoldValueOfSetuphold) {
  Run("(HOLD d (posedge clk) (60))");

  EXPECT_EQ(Limit(TimingCheckKind::kHold), 60u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 13u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 60u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 11u);
}

// Table 32-2 row 3: SETUPHOLD's two values split across three targets -- the
// first to $setup, the second to $hold, and both to $setuphold.
TEST_F(SdfTimingCheckMapping, SetupholdReachesSetupHoldAndSetuphold) {
  Run("(SETUPHOLD d (posedge clk) (70) (80))");

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 70u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 80u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 70u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 80u);

  // $nochange shares this row's two signal names but is a different type, so
  // this row does not reach it and its edge offsets stay where kDesign wrote
  // them, which §31.4.6 makes the 25 and 26 of its third and fourth arguments.
  const auto* nc = Check(mgr, TimingCheckKind::kNochange);
  ASSERT_NE(nc, nullptr);
  EXPECT_EQ(nc->start_edge_offset, 25);
  EXPECT_EQ(nc->end_edge_offset, 26);
}

// Table 32-2 row 4: RECOVERY mirrors SETUP one type over -- $recovery and the
// first value of $recrem, with $recrem's removal value untouched and $removal,
// which shares both signals, not a target.
TEST_F(SdfTimingCheckMapping,
       RecoveryReachesRecoveryAndTheRecoveryValueOfRecrem) {
  Run("(RECOVERY rst (posedge clk) (55))");

  EXPECT_EQ(Limit(TimingCheckKind::kRecovery), 55u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecrem), 55u);
  EXPECT_EQ(Limit2(TimingCheckKind::kRecrem), 18u);
  EXPECT_EQ(Limit(TimingCheckKind::kRemoval), 16u);
}

// Table 32-2 row 5: REMOVAL mirrors HOLD -- $removal and the second value of
// $recrem, written as $recrem(x,v1).
TEST_F(SdfTimingCheckMapping, RemovalReachesRemovalAndTheRemovalValueOfRecrem) {
  Run("(REMOVAL rst (posedge clk) (65))");

  EXPECT_EQ(Limit(TimingCheckKind::kRemoval), 65u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecrem), 17u);
  EXPECT_EQ(Limit2(TimingCheckKind::kRecrem), 65u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecovery), 15u);
}

// Table 32-2 row 6: RECREM's two values reach $recovery, $removal and both
// values of $recrem.
TEST_F(SdfTimingCheckMapping, RecremReachesRecoveryRemovalAndRecrem) {
  Run("(RECREM rst (posedge clk) (75) (85))");

  EXPECT_EQ(Limit(TimingCheckKind::kRecovery), 75u);
  EXPECT_EQ(Limit(TimingCheckKind::kRemoval), 85u);
  EXPECT_EQ(Limit(TimingCheckKind::kRecrem), 75u);
  EXPECT_EQ(Limit2(TimingCheckKind::kRecrem), 85u);
}

// Table 32-2 row 7: SKEW's single value reaches both $skew and $timeskew, and
// not $fullskew, which shares the same two signals.
TEST_F(SdfTimingCheckMapping, SkewReachesSkewAndTimeskew) {
  Run("(SKEW (posedge clk2) (posedge clk) (90))");

  EXPECT_EQ(Limit(TimingCheckKind::kSkew), 90u);
  EXPECT_EQ(Limit(TimingCheckKind::kTimeskew), 90u);
  EXPECT_EQ(Limit(TimingCheckKind::kFullskew), 21u);
  EXPECT_EQ(Limit2(TimingCheckKind::kFullskew), 22u);
}

// Table 32-2 row 8: BIDIRECTSKEW is the two-value skew construct and reaches
// only $fullskew, which is the only two-value skew check. $skew and $timeskew,
// declared on the same signals, are not targets.
TEST_F(SdfTimingCheckMapping, BidirectskewReachesOnlyFullskew) {
  Run("(BIDIRECTSKEW (posedge clk2) (posedge clk) (91) (92))");

  EXPECT_EQ(Limit(TimingCheckKind::kFullskew), 91u);
  EXPECT_EQ(Limit2(TimingCheckKind::kFullskew), 92u);
  EXPECT_EQ(Limit(TimingCheckKind::kSkew), 19u);
  EXPECT_EQ(Limit(TimingCheckKind::kTimeskew), 20u);
}

// Table 32-2 row 9: WIDTH is $width(v1,x) -- the pulse-width limit is annotated
// and the second declared value, the threshold below which a pulse is ignored
// (§31.4.4), is not. $period, declared on the same reference signal, is not a
// target of this row.
//
// The threshold is read off TimingCheckEntry::threshold and limit2 is asserted
// to be zero, §31.4.4 giving $width one timing_check_limit and no second. Issue
// #3418 is that the declared threshold reached limit2 instead and left
// threshold at zero, so this case read the right number out of the wrong
// field.
TEST_F(SdfTimingCheckMapping, WidthReachesWidthLimitButNotItsSecondValue) {
  Run("(WIDTH (posedge clk) (93))");

  EXPECT_EQ(Limit(TimingCheckKind::kWidth), 93u);
  EXPECT_EQ(Threshold(TimingCheckKind::kWidth), 5u);
  EXPECT_EQ(Limit2(TimingCheckKind::kWidth), 0u);
  EXPECT_EQ(Limit(TimingCheckKind::kPeriod), 24u);
}

// Table 32-2 row 10: PERIOD reaches $period and nothing else, though $width is
// declared on the same reference signal and with no data signal either.
TEST_F(SdfTimingCheckMapping, PeriodReachesOnlyPeriod) {
  Run("(PERIOD (posedge clk) (94))");

  EXPECT_EQ(Limit(TimingCheckKind::kPeriod), 94u);
  EXPECT_EQ(Limit(TimingCheckKind::kWidth), 23u);
}

// Table 32-2 row 11: NOCHANGE's two values are $nochange's two edge offsets.
TEST_F(SdfTimingCheckMapping, NochangeReachesNochangeEdgeOffsets) {
  Run("(NOCHANGE d (posedge clk) (7) (8))");

  const auto* nc = Check(mgr, TimingCheckKind::kNochange);
  ASSERT_NE(nc, nullptr);
  EXPECT_EQ(nc->start_edge_offset, 7);
  EXPECT_EQ(nc->end_edge_offset, 8);

  // The three checks declared on the same two signals are all of other types,
  // so this row leaves every one of them alone.
  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 11u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 12u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 13u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 14u);
}

// The negative form of the whole table: annotation matches by signal name as
// well as by type, so a check naming a signal no declaration uses reaches
// nothing. Every declared value survives untouched.
TEST_F(SdfTimingCheckMapping, CheckOnAnUndeclaredSignalReachesNothing) {
  Run("(SETUP d (posedge nosuchclk) (99))");

  EXPECT_EQ(Limit(TimingCheckKind::kSetup), 11u);
  EXPECT_EQ(Limit(TimingCheckKind::kHold), 12u);
  EXPECT_EQ(Limit(TimingCheckKind::kSetuphold), 13u);
  EXPECT_EQ(Limit2(TimingCheckKind::kSetuphold), 14u);
}

// The single-value rows end-to-end: what a row annotates is the value the
// check runs on afterwards, not just a field that happens to hold it. $skew
// reports a violation when the data event trails the reference by more than its
// limit (§31.4.1), so a gap of 50 violates the declared limit of 19 and stops
// violating once SKEW raises it to 90. The verdict flipping is the annotated
// value being used.
TEST_F(SdfTimingCheckMapping, AnnotatedSkewLimitIsTheOneTheCheckRunsOn) {
  EXPECT_TRUE(mgr.CheckSkewViolation("clk", 100, "clk2", 150));

  Run("(SKEW (posedge clk2) (posedge clk) (90))");

  EXPECT_FALSE(mgr.CheckSkewViolation("clk", 100, "clk2", 150));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk", 100, "clk2", 200));
}

// The two-value rows end-to-end, and the sharper claim: v1 and v2 reach the
// slots the table assigns them, which only shows at run time. $setuphold judges
// a data event arriving before the reference against its setup value and one
// arriving after against its hold value (§31.3.3). After SETUPHOLD supplies 70
// and 80, a gap of 75 clears the setup side and violates the hold side -- an
// asymmetry only possible if 70 went to the first slot and 80 to the second.
TEST_F(SdfTimingCheckMapping, SetupholdValuesReachTheSlotsTheyRunOn) {
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "d", 25));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "d", 175));

  Run("(SETUPHOLD d (posedge clk) (70) (80))");

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "d", 25));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "d", 175));
}

// The three declarations §32.4.2 works its condition/edge examples against:
// they agree on type and on both signal names and differ only in the edge
// (§31.5) and the conditioned event (§31.7) on the reference signal.
const char* const kConditionedDesign =
    "module t(input data, input clk, input mode);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(posedge clk &&& mode, data, 1, 1, ntf);\n"
    "    $setuphold(negedge clk &&& !mode, data, 2, 2, ntf);\n"
    "    $setuphold(edge clk, data, 3, 3, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

// Same three, with the condition sitting on the *data* signal instead: §32.4.2
// says either signal of a timing check may carry one.
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

  // The declaration carrying a given reference edge and condition, which is
  // what tells the three siblings apart.
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

// An SDF check that puts no condition and no edge on either of its signals
// matches every corresponding declaration, whether or not that declaration
// carries a condition of its own. All three siblings take the new values.
TEST_F(SdfTimingCheckConditionMatching,
       BareCheckReachesEveryCorrespondingDeclaration) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data clk (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 5, 6);
}

// Once the SDF check carries an edge, that edge has to match before annotation
// happens. Only the posedge declaration takes the new values -- its condition
// is no obstacle, because the SDF check names none. The negedge sibling and the
// edge-control sibling (§31.5) keep what they were declared with.
TEST_F(SdfTimingCheckConditionMatching,
       EdgeOnTheSdfCheckMustMatchBeforeAnnotation) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (posedge clk) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 2, 2);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

// With a condition *and* an edge on the SDF check both have to match, and here
// no declaration matches on both: the posedge sibling is conditioned the other
// way, the sibling conditioned this way has the wrong edge, and the third
// carries no condition at all. Nothing is annotated.
TEST_F(SdfTimingCheckConditionMatching, ConditionAndEdgeTogetherMustBothMatch) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (COND !mode (posedge clk)) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 1, 1);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 2, 2);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

// The accepting half of the same input form: a condition and an edge together,
// where one declaration does carry both. That one is annotated -- matching on
// both is what the rule asks for, not an obstacle -- while the sibling agreeing
// only on the condition and the sibling agreeing on neither are left alone.
TEST_F(SdfTimingCheckConditionMatching,
       ConditionAndEdgeTogetherAnnotateTheDeclarationCarryingBoth) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (COND mode (posedge clk)) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 2, 2);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

// A condition alone, with no edge, still has to match: the one declaration
// conditioned the same way takes the values and its two siblings -- one
// conditioned the other way, one unconditioned -- do not.
TEST_F(SdfTimingCheckConditionMatching,
       ConditionOnTheReferenceSignalMustMatch) {
  Build(kConditionedDesign);
  Run("(SETUPHOLD data (COND !mode clk) (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 1, 1);
  ExpectLimits(Declared(SpecifyEdge::kNegedge, "!mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kEdge, ""), 3, 3);
}

// The condition may equally sit on the SDF check's data signal, and it takes
// part in matching from there: only the declaration conditioned the same way is
// annotated. Were a data-signal condition dropped, the check would read as
// unconditioned and would reach all three.
TEST_F(SdfTimingCheckConditionMatching, ConditionOnTheDataSignalMustMatch) {
  Build(kDataConditionedDesign);
  Run("(SETUPHOLD (COND !mode data) clk (5) (6))");

  ExpectLimits(Declared(SpecifyEdge::kPosedge, "mode"), 1, 1);
  ExpectLimits(Declared(SpecifyEdge::kPosedge, "!mode"), 5, 6);
  ExpectLimits(Declared(SpecifyEdge::kPosedge, ""), 3, 3);
}

// Two declarations agreeing on everything but the edge on their *data* signal,
// which §32.4.2 says a timing check's signals may carry just as its reference
// signal may.
const char* const kDataEdgeDesign =
    "module t(input data, input clk);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(posedge clk, posedge data, 1, 1, ntf);\n"
    "    $setuphold(posedge clk, negedge data, 2, 2, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

// An edge on the SDF check's data signal has to match too: the declaration
// carrying the same data edge is annotated and the one carrying the other edge
// is left alone.
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

// The other side of the edge input form: declarations that carry *no* edge at
// all. Neither of these puts an edge on its data signal, and the first puts
// none on its reference signal either.
const char* const kNoEdgeDesign =
    "module t(input data, input clk);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(clk, data, 1, 1, ntf);\n"
    "    $setuphold(posedge clk, data, 2, 2, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

// An edge on the SDF check has to be matched by an edge on the declaration --
// carrying none is not the same as carrying any. The edgeless declaration is
// left alone and only the one declaring that same edge is annotated.
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

// The same for the data signal: an SDF data edge finds no match in declarations
// that put no edge on their data signal, so neither of them is annotated even
// though both agree on type and on both signal names. Nothing being annotated
// is the point here, and it is not vacuous: the test above drives this very
// same SDF entry and shows it does reach a declaration that carries that edge.
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

// Three declarations differing only in the pair of edges they carry, so a check
// that names an edge on both of its signals has exactly one of them to land on.
const char* const kBothEdgeDesign =
    "module t(input data, input clk);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    $setuphold(posedge clk, posedge data, 1, 1, ntf);\n"
    "    $setuphold(posedge clk, negedge data, 2, 2, ntf);\n"
    "    $setuphold(negedge clk, posedge data, 3, 3, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

// Both signals of an SDF timing check may carry an edge at once, and then both
// have to match: agreeing on one of the two is not enough. Only the declaration
// pairing the same reference edge with the same data edge is annotated; the two
// that agree on just one of them keep their declared values.
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

// The rest of this file is about which module *instance* an SDF timing check
// reaches. §32.4.2 settles which declared check a record lands on -- its type,
// its two signals, their edges and their conditions -- and §32.9 settles which
// instance it lands in: "the SDF annotator uses the hierarchy level of the
// specified instance for running the annotation", so a record written under
// (INSTANCE u_first) reaches u_first and no other instance of that cell. §31.2
// puts a system timing check in a specify block and §30.3 has that block
// "appear inside a module declaration", so two instances of one cell declare
// checks whose signals are spelled identically, and the instance is the only
// thing that separates them.
//
// Every case below hands AnnotateSdfToManager a design root, which no case
// above does. SdfCellInstancePrefix (src/simulator/sdf_parser.h) answers empty
// for an empty design root, so an annotation made without one carries the empty
// prefix and could not name an instance however strictly the prefix were
// compared; the root is what makes the SDF instance path design-relative. The
// cases above pass no root, and their declarations and their annotations both
// stand at the empty prefix for that reason.
//
// Every case builds its SystemVerilog side by elaborating, lowering and running
// real source, rather than by registering one ModuleDecl's checks the way the
// cases above do. Lowerer::RegisterDesignTiming files each instance's specify
// block under that instance's own hierarchical prefix, and that is what gives a
// case two entries to tell apart.
//
// The limits are picked so that no two quantities a case tells apart share a
// value. 31 is what the two-instance cell declares, 41 and 59 are what the two
// records of the first case annotate, and 67 is what the single record of the
// second annotates: a check reached by the wrong record reads as another of
// those, a check never reached reads as 31, and neither can be mistaken for the
// right answer. The design-root case declares 23 at the top and 37 in the
// instance and annotates 83, all three distinct. No limit is 0, which is what
// TimingCheckEntry::limit holds before a limit expression is evaluated into it.

// The SpecifyManager `source` leaves on `f.ctx` once it has been elaborated,
// lowered and run -- the one Lowerer::Lower installed, which holds each
// instance's checks under that instance's prefix. Null when the source did not
// elaborate cleanly, so a case asserts on the pointer before annotating onto
// it.
SpecifyManager* ManagerAfterRun(const std::string& source, SimFixture& f) {
  auto* design = ElaborateSrc(source, f);
  if (design == nullptr || f.has_errors) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.GetSpecifyManager();
}

// Annotates real SDF text onto a manager filled by a run, naming the module the
// design was elaborated as. §32.9's instance paths are written from the design
// root, and that fifth argument is what AnnotateSdfToManager measures them
// against.
void AnnotateUnderDesignRoot(const std::string& sdf, SpecifyManager& mgr,
                             std::string_view design_root) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, /*scope=*/{}, design_root);
}

// One CELL record carrying one SETUP entry on the signals `d` and `clk`. An SDF
// timing check writes its data signal before its reference signal -- §32.4.2's
// own example is (SETUPHOLD data clk (3) (4)) -- so `d` is the data signal here
// and `clk` the reference, which is also the order §31.2's
// $setup(data_event, reference_event, timing_check_limit) writes them in.
std::string SetupRecord(const std::string& cell_type,
                        const std::string& instance, const std::string& limit) {
  return "  (CELL (CELLTYPE \"" + cell_type + "\") (INSTANCE " + instance +
         ") (TIMINGCHECK (SETUP d (posedge clk) (" + limit + "))))\n";
}

std::string DelayFileOf(const std::string& records) {
  return "(DELAYFILE\n" + records + ")\n";
}

// The limit of the one $setup registered under the instance whose hierarchical
// prefix is `prefix`. Both fields are needed: §31.2 has a timing check name its
// signals by the port names of the module declaring it, so two instances of one
// cell register checks agreeing on kind, on ref_signal and on data_signal.
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

// One cell instantiated twice under a top named `top`, so the two instances
// declare $setup checks spelled identically and separated only by their
// prefixes, "u_first." and "u_second.". The cell stands first because
// ElaborateSrc (lib/cpp/test_fixtures/fixture_simulator.h) elaborates
// cu->modules.back()->name. It is not named `cell`, which §33.4 gives to a
// config declaration's cell clause.
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

// §32.9: each record annotates the instance its (INSTANCE ...) operand names,
// so two records naming two instances of one cell give those instances
// different limits for the identically spelled §31.2 check both declared. 41
// and 59 differ from one another and from the 31 the cell declared, so a check
// reached by the other instance's record and a check reached by no record read
// as different wrong numbers.
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

// §32.9: a file that names one instance annotates that instance alone, so the
// other instance of the same cell keeps the limit its own declaration gave it.
// The declared 31 is what says the record stopped where its operand did; 67 is
// distinct from it and from the 41 and 59 the case above annotates, so a check
// reached by the record reads as neither.
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

// A top declaring a $setup of its own beside an instance declaring one, so the
// two checks agree on everything §32.4.2 matches on and differ only in the
// instance: the top's prefix is empty and the instance's is "u_inner.".
const char* const kRootAndInstanceDesign =
    "module rooted_cell(input d, input clk, output q);\n"
    "  specify\n"
    "    $setup(d, posedge clk, 37);\n"
    "  endspecify\n"
    "endmodule\n"
    "module top;\n"
    "  logic d;\n"
    "  logic clk;\n"
    "  logic inner_q;\n"
    "  rooted_cell u_inner(1'b0, 1'b0, inner_q);\n"
    "  specify\n"
    "    $setup(d, posedge clk, 23);\n"
    "  endspecify\n"
    "endmodule\n";

// §32.9: a record whose instance path is the design root itself names the top,
// whose prefix is empty, and reaches the check the top declared. The empty
// prefix names that one instance rather than every instance, so the check
// declared inside u_inner keeps its own 37 while the top takes 83.
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

}  // namespace
