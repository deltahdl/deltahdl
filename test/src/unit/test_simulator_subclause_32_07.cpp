#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "fixture_specify_manager.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

struct Design : SdfDesign {
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    const ModuleDecl& top = Top();
    AddPathsAndTimingChecks(top);

    RegisterPathPulseSpecparams(top, f, mgr);
    return true;
  }

  SdfAnnotationResult Annotate(const std::string& sdf,
                               SdfMtm mtm = SdfMtm::kTypical) {
    SdfFile file;
    EXPECT_TRUE(ParseSdf(sdf, file));
    return AnnotateSdfToManager(file, mgr, mtm);
  }

  const PathDelay* Path(std::string_view condition = {}) const {
    for (const auto& pd : mgr.GetPathDelays()) {
      if (pd.src_port == "A" && pd.dst_port == "Z" &&
          pd.condition == condition) {
        return &pd;
      }
    }
    return nullptr;
  }

  const TimingCheckEntry* Check(TimingCheckKind kind) const {
    for (const auto& tc : mgr.GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }
};

std::string SdfCellText(const std::string& sections) {
  return "(DELAYFILE (CELL (CELLTYPE \"c\") (INSTANCE u1) " + sections + "))";
}

std::string SdfAbsolute(const std::string& body) {
  return SdfCellText("(DELAY (ABSOLUTE " + body + "))");
}

std::string SdfIncrement(const std::string& body) {
  return SdfCellText("(DELAY (INCREMENT " + body + "))");
}

const char* const kPathWithLimitsSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kLimitsOfThreeSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (3, 3);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kPlainPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kFiftyDelayPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 50;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kUnitDelayPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 1;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kRiseFallPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = (20, 80);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kPathSpecificLimitsSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$A$Z = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kConditionalPathSrc =
    "module c(input A, input mode, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    if (mode) (A => Z) = 50;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kCheckedPathSrc =
    "module c(input A, input D, input CK, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "    $setup(D, posedge CK, 5);\n"
    "  endspecify\n"
    "endmodule\n";

TEST(SdfPulseLimitAnnotation, DefaultPercentagesMakeEachLimitTheWholeDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));
  ASSERT_NE(d.Path(), nullptr);
  ASSERT_EQ(d.Path()->reject_limit[0], 21u);

  d.Annotate(SdfAbsolute("(IOPATH A Z (5) (5))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 5u);
  EXPECT_EQ(pd->reject_limit[0], 5u);
  EXPECT_EQ(pd->error_limit[0], 5u);
  EXPECT_EQ(pd->reject_limit[1], 5u);
  EXPECT_EQ(pd->error_limit[1], 5u);
}

TEST(SdfPulseLimitAnnotation, InvocationPercentagesScaleTheAnnotatedDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));
  d.mgr.SetGlobalPulseLimitPercents(40, 80);

  d.Annotate(SdfAbsolute("(IOPATH A Z (5))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 5u);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 4u);
}

TEST(SdfPulseLimitAnnotation, DeviceDelayDerivesTheLimitsToo) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));
  d.mgr.SetGlobalPulseLimitPercents(40, 80);

  d.Annotate(SdfAbsolute("(DEVICE (5))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 5u);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 4u);
}

TEST(SdfPulseLimitAnnotation, PercentagesDeriveEachSlotFromItsOwnDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));
  d.mgr.SetGlobalPulseLimitPercents(40, 80);

  d.Annotate(SdfAbsolute("(IOPATH A Z (10) (20))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 4u);
  EXPECT_EQ(pd->error_limit[0], 8u);
  EXPECT_EQ(pd->reject_limit[1], 8u);
  EXPECT_EQ(pd->error_limit[1], 16u);
}

TEST(SdfPulseLimitAnnotation, LimitsDeriveFromTheSelectedMinimumMember) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));
  d.mgr.SetGlobalPulseLimitPercents(40, 80);

  d.Annotate(SdfAbsolute("(IOPATH A Z (4:5:9))"), SdfMtm::kMinimum);

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 4u);
  EXPECT_EQ(pd->reject_limit[0], 1u);
  EXPECT_EQ(pd->error_limit[0], 3u);
}

TEST(SdfPulseLimitAnnotation, LimitsDeriveFromTheSelectedMaximumMember) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));
  d.mgr.SetGlobalPulseLimitPercents(40, 80);

  d.Annotate(SdfAbsolute("(IOPATH A Z (4:5:9))"), SdfMtm::kMaximum);

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 9u);
  EXPECT_EQ(pd->reject_limit[0], 3u);
  EXPECT_EQ(pd->error_limit[0], 7u);
}

TEST(SdfPulseLimitAnnotation, ConditionalEntryDerivesLimitsOnThePathItNames) {
  Design d;
  ASSERT_TRUE(d.Build(kConditionalPathSrc));
  d.mgr.SetGlobalPulseLimitPercents(40, 80);

  d.Annotate(SdfAbsolute("(COND mode (IOPATH A Z (5)))"));

  const auto* conditional = d.Path("mode");
  const auto* plain = d.Path();
  ASSERT_NE(conditional, nullptr);
  ASSERT_NE(plain, nullptr);
  EXPECT_EQ(conditional->delays[0], 5u);
  EXPECT_EQ(conditional->reject_limit[0], 2u);
  EXPECT_EQ(conditional->error_limit[0], 4u);
  EXPECT_EQ(plain->delays[0], 40u);
  EXPECT_EQ(plain->reject_limit[0], 21u);
}

TEST(SdfPulseLimitAnnotation, ErrorPercentageBelowRejectRisesToMeetIt) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));
  d.mgr.SetGlobalPulseLimitPercents(60, 20);

  d.Annotate(SdfAbsolute("(IOPATH A Z (10) (10))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 6u);
  EXPECT_EQ(pd->error_limit[0], 6u);
}

TEST(SdfPulseLimitAnnotation, TimingConstraintAnnotationCalculatesNoLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kCheckedPathSrc));
  d.mgr.SetGlobalPulseLimitPercents(40, 80);

  d.Annotate(SdfCellText("(TIMINGCHECK (SETUP D (posedge CK) (9)))"));

  ASSERT_NE(d.Check(TimingCheckKind::kSetup), nullptr);
  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 9u);
  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

TEST(SdfPulseLimitAnnotation, EmptyPulseFieldsHoldTheDeclaredLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) () ()))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 5u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

TEST(SdfPulseLimitAnnotation, AnEmptyErrorFieldHoldsOnlyTheErrorLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) (2) ()))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

TEST(SdfPulseLimitAnnotation, AnEmptyRejectFieldHoldsOnlyTheRejectLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) () (4)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 4u);
}

TEST(SdfPulseLimitAnnotation, AnEntryStatingBothLimitsHoldsNeither) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) (2) (4)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 4u);
}

TEST(SdfPulseLimitAnnotation, EmptyFieldsHoldPathSpecificDeclaredLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kPathSpecificLimitsSrc));
  ASSERT_NE(d.Path(), nullptr);
  ASSERT_EQ(d.Path()->reject_limit[0], 21u);

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) () ()))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 5u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

TEST(SdfPulseLimitAnnotation, EmptyFieldsHoldWhatAnEarlierConstructLeft) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(
      SdfAbsolute("(PATHPULSE A Z (21) (34))"
                  " (IOPATH A Z ((5) () ()) ((6) () ()))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 5u);
  EXPECT_EQ(pd->delays[1], 6u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

TEST(SdfPulseLimitAnnotation, IncrementBelowZeroLeavesEachLimitAtZero) {
  Design d;
  ASSERT_TRUE(d.Build(kLimitsOfThreeSrc));
  ASSERT_NE(d.Path(), nullptr);
  ASSERT_EQ(d.Path()->reject_limit[0], 3u);

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-4) (-5)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->reject_limit[0], 0u);
  EXPECT_EQ(pd->error_limit[0], 0u);
  EXPECT_EQ(pd->reject_limit[1], 0u);
  EXPECT_EQ(pd->error_limit[1], 0u);
}

TEST(SdfPulseLimitAnnotation, IncrementSubtractsWhatTheLimitCanAbsorb) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-4) (-5)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 17u);
  EXPECT_EQ(pd->error_limit[0], 29u);
}

TEST(SdfPulseLimitAnnotation, IncrementAddsToTheLimitAlreadyInPlace) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (4) (5)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 25u);
  EXPECT_EQ(pd->error_limit[0], 39u);
}

TEST(SdfPulseLimitAnnotation, IncrementHoldsOnlyTheLimitThatWouldGoNegative) {
  Design d;
  ASSERT_TRUE(d.Build(kLimitsOfThreeSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-5) (2)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 0u);
  EXPECT_EQ(pd->error_limit[0], 5u);
}

TEST(SdfPulseLimitAnnotation,
     IncrementReadsTheSelectedMinimumMemberWithItsSign) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-4:6:-8) (-5:7:-9)))"),
             SdfMtm::kMinimum);

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 17u);
  EXPECT_EQ(pd->error_limit[0], 29u);
}

TEST(SdfPulseLimitAnnotation,
     IncrementReadsTheSelectedTypicalMemberWithItsSign) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-4:6:-8) (-5:7:-9)))"),
             SdfMtm::kTypical);

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 27u);
  EXPECT_EQ(pd->error_limit[0], 41u);
}

TEST(SdfPulseLimitAnnotation,
     IncrementReadsTheSelectedMaximumMemberWithItsSign) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-4:6:-8) (-5:7:-9)))"),
             SdfMtm::kMaximum);

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 13u);
  EXPECT_EQ(pd->error_limit[0], 25u);
}

TEST(SdfPulseLimitAnnotation, IncrementHoldsOnlyTheSlotThatWouldGoNegative) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(
      SdfCellText("(DELAY (ABSOLUTE (IOPATH A Z (10) (40))))"
                  " (DELAY (INCREMENT (IOPATH A Z (() (-20) (-20)))))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 0u);
  EXPECT_EQ(pd->error_limit[0], 0u);
  EXPECT_EQ(pd->reject_limit[1], 20u);
  EXPECT_EQ(pd->error_limit[1], 20u);
}

TEST(SdfPulseLimitAnnotation, IncrementDelayMovesNoPulseLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z ((6) () ()))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 46u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

TEST(SdfPulseLimitAnnotation, PathpulseLeavesThePathDelayWhereItWas) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (10) (20))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->reject_limit[0], 10u);
  EXPECT_EQ(pd->error_limit[0], 20u);
}

TEST(SdfPulseLimitAnnotation, PathpulsepercentLeavesThePathDelayWhereItWas) {
  Design d;
  ASSERT_TRUE(d.Build(kFiftyDelayPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSEPERCENT A Z (25) (75))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 50u);
  EXPECT_EQ(pd->reject_limit[0], 12u);
  EXPECT_EQ(pd->error_limit[0], 37u);
}

TEST(SdfPulseLimitAnnotation, PathpulseWithOneValueSetsBothLimitsFromIt) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (10))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->reject_limit[0], 10u);
  EXPECT_EQ(pd->error_limit[0], 10u);
}

TEST(SdfPulseLimitAnnotation,
     PathpulsepercentWithOneValueSetsBothLimitsFromIt) {
  Design d;
  ASSERT_TRUE(d.Build(kFiftyDelayPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSEPERCENT A Z (25))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 50u);
  EXPECT_EQ(pd->reject_limit[0], 12u);
  EXPECT_EQ(pd->error_limit[0], 12u);
}

TEST(SdfPulseLimitAnnotation, PathpulseLimitsAboveTheDelayBehaveAsTheDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (50) (90))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(EffectivePulseLimit(pd->reject_limit[0], pd->delays[0]), 40u);
  EXPECT_EQ(EffectivePulseLimit(pd->error_limit[0], pd->delays[0]), 40u);
}

TEST(SdfPulseLimitAnnotation, PathpulseLeavesALimitBelowTheDelayAlone) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (20) (90))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(EffectivePulseLimit(pd->reject_limit[0], pd->delays[0]), 20u);
  EXPECT_EQ(EffectivePulseLimit(pd->error_limit[0], pd->delays[0]), 40u);
}

TEST(SdfPulseLimitAnnotation, PathpulseMeasuresEachSlotAgainstItsOwnDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kRiseFallPathSrc));
  ASSERT_NE(d.Path(), nullptr);
  ASSERT_EQ(d.Path()->delays[0], 20u);
  ASSERT_EQ(d.Path()->delays[1], 80u);

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (50) (60))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(EffectivePulseLimit(pd->reject_limit[0], pd->delays[0]), 20u);
  EXPECT_EQ(EffectivePulseLimit(pd->error_limit[0], pd->delays[0]), 20u);
  EXPECT_EQ(EffectivePulseLimit(pd->reject_limit[1], pd->delays[1]), 50u);
  EXPECT_EQ(EffectivePulseLimit(pd->error_limit[1], pd->delays[1]), 60u);
}

TEST(SdfPulseLimitAnnotation, PathpulsepercentOverAHundredBehavesAsTheDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kFiftyDelayPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSEPERCENT A Z (120) (150))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(EffectivePulseLimit(pd->reject_limit[0], pd->delays[0]), 50u);
  EXPECT_EQ(EffectivePulseLimit(pd->error_limit[0], pd->delays[0]), 50u);
}

TEST(SdfPulseLimitAnnotation, PathpulseLimitsAboveTheDelayOutliveIt) {
  Design d;
  ASSERT_TRUE(d.Build(kUnitDelayPathSrc));

  d.Annotate(
      SdfAbsolute("(PATHPULSE A Z (2) (3))"
                  " (IOPATH A Z ((4) () ()) ((6) () ()))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 4u);
  EXPECT_EQ(pd->delays[1], 6u);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 3u);
  EXPECT_EQ(pd->reject_limit[1], 2u);
  EXPECT_EQ(pd->error_limit[1], 3u);
}

TEST(SdfPulseLimitAnnotation, PathpulseIncrementSubtractsFromTheLimitsInPlace) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(PATHPULSE A Z (-4) (-5))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->reject_limit[0], 17u);
  EXPECT_EQ(pd->error_limit[0], 29u);
}

TEST(SdfPulseLimitAnnotation, PathpulseIncrementBelowZeroLeavesLimitsAtZero) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(PATHPULSE A Z (-25) (-40))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 0u);
  EXPECT_EQ(pd->error_limit[0], 0u);
}

TEST(SdfPulseLimitAnnotation, PathpulseIncrementWithOneValueMovesBothLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(PATHPULSE A Z (5))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 26u);
  EXPECT_EQ(pd->error_limit[0], 39u);
}

TEST(SdfPulseLimitAnnotation,
     PathpulseIncrementAboveTheDelayBehavesAsTheDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(PATHPULSE A Z (30) (30))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(EffectivePulseLimit(pd->reject_limit[0], pd->delays[0]), 40u);
  EXPECT_EQ(EffectivePulseLimit(pd->error_limit[0], pd->delays[0]), 40u);
}

TEST(SdfPulseLimitAnnotation, PathpulsepercentIncrementAddsAShareOfTheDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kFiftyDelayPathSrc));

  d.Annotate(
      SdfCellText("(DELAY (ABSOLUTE (PATHPULSEPERCENT A Z (25) (75))))"
                  " (DELAY (INCREMENT (PATHPULSEPERCENT A Z (10) (10))))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 17u);
  EXPECT_EQ(pd->error_limit[0], 42u);
}

}  // namespace
