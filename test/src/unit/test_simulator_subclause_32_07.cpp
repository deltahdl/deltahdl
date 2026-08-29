#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "fixture_specify_manager.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.7 is about what an SDF construct leaves on a module path's two pulse
// limits. Both halves of that are produced by SystemVerilog the design was
// written in: the delay a limit is derived from or measured against comes from
// §30.5's module path assignment, and the limits a construct finds already in
// place come from §30.7.1's PATHPULSE$ specparam. So every test here builds its
// design side from real source -- parsed, elaborated and lowered, then handed
// to the production collectors -- and its SDF side from real SDF text handed to
// ParseSdf. Nothing on either side is hand-assembled.
struct Design : SdfDesign {
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    const ModuleDecl& top = Top();
    AddPathsAndTimingChecks(top);

    // A PATHPULSE$ specparam is how a path's pulse limits come to hold a value
    // before any annotation runs, so it is read from the declaration and
    // applied through the production resolver.
    RegisterPathPulseSpecparams(top, f, mgr);
    return true;
  }

  // `mtm` picks which member of a min:typ:max value the annotation reads, which
  // is a choice every rule here inherits: the quantity a limit is derived from
  // or changed by is whichever member was selected.
  SdfAnnotationResult Annotate(const std::string& sdf,
                               SdfMtm mtm = SdfMtm::kTypical) {
    SdfFile file;
    EXPECT_TRUE(ParseSdf(sdf, file));
    return AnnotateSdfToManager(file, mgr, mtm);
  }

  // The whole module path delay entry, so a test can read the delay and both
  // pulse limits of any transition slot rather than a single value. Every
  // module below declares its paths between the same two terminals, so
  // `condition` is what tells two of them apart -- empty for a plain path, the
  // condition text for a state-dependent one.
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

// Wraps whatever sections a test writes in the DELAYFILE/CELL structure an SDF
// file always supplies, so each test writes only the construct under test.
std::string SdfCellText(const std::string& sections) {
  return "(DELAYFILE (CELL (CELLTYPE \"c\") (INSTANCE u1) " + sections + "))";
}

// One ABSOLUTE DELAY section, the mode that states a value outright.
std::string SdfAbsolute(const std::string& body) {
  return SdfCellText("(DELAY (ABSOLUTE " + body + "))");
}

// One INCREMENT DELAY section, the mode that states a change to the value
// already in place.
std::string SdfIncrement(const std::string& body) {
  return SdfCellText("(DELAY (INCREMENT " + body + "))");
}

// A module path with pulse limits already set, by a module-wide PATHPULSE$
// declaration rather than by anything in the SDF file. 21 and 34 differ from
// each other, from the declared delay and from every value the tests annotate,
// so a limit that was held apart from a limit that was recomputed and a limit
// that was overwritten are three distinguishable outcomes.
const char* const kPathWithLimitsSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

// §32.7's own starting state for the INCREMENT example: both pulse limits at 3,
// which the negative amounts the example annotates carry below zero.
const char* const kLimitsOfThreeSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (3, 3);\n"
    "  endspecify\n"
    "endmodule\n";

// A module path carrying a delay and nothing else, for the constructs that
// annotate the limits outright and so do not care what was there before.
const char* const kPlainPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "  endspecify\n"
    "endmodule\n";

// The same, with a delay whose quarter and three quarters are whole numbers, so
// a percentage-of-the-delay limit lands on a value distinct from both the delay
// and the percentage that produced it.
const char* const kFiftyDelayPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 50;\n"
    "  endspecify\n"
    "endmodule\n";

// A module path whose rise and fall delays differ (§30.5.1), so a single pulse
// limit annotated across the path meets two different delays and each
// transition slot can be told apart from the others.
const char* const kRiseFallPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = (20, 80);\n"
    "  endspecify\n"
    "endmodule\n";

// The path-specific spelling of the same §30.7.1 declaration, which reaches the
// path by naming its two terminals rather than by covering the whole module. It
// is the other way the limits an annotation finds already in place are
// produced.
const char* const kPathSpecificLimitsSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$A$Z = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

// One plain module path and one state-dependent path between the same two
// terminals, so an SDF entry written under a condition (§32.4.1) reaches only
// one of them and what it did to that path can be told from what it left alone.
const char* const kConditionalPathSrc =
    "module c(input A, input mode, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    if (mode) (A => Z) = 50;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

// A module path beside a timing check, so an SDF file annotating a timing
// constraint rather than a delay has somewhere to land while the path's pulse
// limits stand by to be looked at.
const char* const kCheckedPathSrc =
    "module c(input A, input D, input CK, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "    $setup(D, posedge CK, 5);\n"
    "  endspecify\n"
    "endmodule\n";

// ---------------------------------------------------------------------------
// The pulse limits a delay annotation does not state are calculated from the
// reject and error percentage settings, which are 100% until an invocation
// option says otherwise.
// ---------------------------------------------------------------------------

// With the settings left alone, 100% of the annotated delay is the annotated
// delay, so both limits land there. The path arrives at the annotation holding
// limits of its own, which is what makes the outcome a calculation rather than
// the limits simply being left as they were.
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

// §32.7's own example of the calculation: with the invocation options putting
// the reject limit at 40% and the error limit at 80%, an annotated delay of 5
// leaves a reject limit of 2 and an error limit of 4. The two percentages are
// read separately, so the two limits land on different values.
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

// The calculation runs per transition, and the percentages are of whatever
// delay the entry annotates rather than of a fixed quantity: an entry giving
// the rising and the falling transition different delays leaves each slot's
// limits derived from that slot's own delay.
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

// A delay value may be written as three members and the annotation reads the
// one selected for the run. Selecting the first member makes 4 the delay the
// limits are derived from, so the limits follow the selection rather than the
// written text.
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

// The same value with the third member selected: a different delay is
// annotated, so different limits are derived from the same SDF text.
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

// The entry may be written under a condition (§32.4.1), which narrows it to the
// state-dependent path declared with that condition. The limits are derived
// there and the plain path between the same terminals keeps both the delay and
// the limits its declarations gave it.
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

// The two settings are not independent of each other: a reject limit is never
// wider than the error limit, so settings that would put the error percentage
// below the reject percentage give both limits the reject percentage.
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

// The negative form: the calculation belongs to the annotation of delays, and a
// timing constraint is not one. A TIMINGCHECK section lands its constraint on
// the declared check and leaves the path's pulse limits exactly as the module
// declared them, percentage settings notwithstanding.
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

// ---------------------------------------------------------------------------
// An entry that writes a pulse limit as an empty pair of parentheses is not
// annotating that limit, so the limit already in place stands.
// ---------------------------------------------------------------------------

// Holding a limit, recalculating it and overwriting it all name different
// values here, so the outcome says which of the three happened: the limits the
// PATHPULSE$ declaration put in place are what the path is left holding, not
// the 5 the newly annotated delay would calculate.
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

// The two limits are decided one at a time: an entry may state the reject limit
// and leave the error limit where it was.
TEST(SdfPulseLimitAnnotation, AnEmptyErrorFieldHoldsOnlyTheErrorLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) (2) ()))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

// And the other way round, which is what makes it two decisions rather than one
// covering both limits.
TEST(SdfPulseLimitAnnotation, AnEmptyRejectFieldHoldsOnlyTheRejectLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) () (4)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 4u);
}

// The fourth combination of the two fields, and the negative form of the rule:
// an entry that writes both limits holds neither, so both land on the values
// the entry states rather than on the declared ones.
TEST(SdfPulseLimitAnnotation, AnEntryStatingBothLimitsHoldsNeither) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfAbsolute("(IOPATH A Z ((5) (2) (4)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 4u);
}

// The limits an empty field holds may have been put in place by the other
// §30.7.1 spelling, which names the path's two terminals instead of covering
// the module. What holds is whatever the path carries, however it got there.
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

// A declaration is not the only producer: within one run of constructs (§32.5)
// an earlier PATHPULSE puts the limits in place and the empty fields of a later
// entry hold those, which is what lets the pair say what one entry stating both
// limits alongside its delays says.
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

// ---------------------------------------------------------------------------
// In INCREMENT mode a pulse limit value is a change to the limit in place, and
// a change that would carry a limit below zero leaves it at zero.
// ---------------------------------------------------------------------------

// §32.7's own example: with both pulse limits at 3, amounts of -4 and -5 leave
// both limits at 0 rather than below it. Every transition slot is carried the
// same way, and the empty delay field means the path's delay is untouched.
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

// The same two amounts against limits high enough to absorb them: each limit
// comes down by exactly what the entry wrote, which is what tells subtraction
// apart from a blanket reset to zero and from the sign being dropped.
TEST(SdfPulseLimitAnnotation, IncrementSubtractsWhatTheLimitCanAbsorb) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-4) (-5)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 17u);
  EXPECT_EQ(pd->error_limit[0], 29u);
}

// The raising half of the same mode: an amount written without a minus sign
// adds to the limit in place instead of replacing it.
TEST(SdfPulseLimitAnnotation, IncrementAddsToTheLimitAlreadyInPlace) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (4) (5)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 25u);
  EXPECT_EQ(pd->error_limit[0], 39u);
}

// Zero is where a limit is held, not where the whole entry is abandoned: the
// reject limit the amount carries below zero stops there while the error limit
// the same entry raises still arrives at its own value.
TEST(SdfPulseLimitAnnotation, IncrementHoldsOnlyTheLimitThatWouldGoNegative) {
  Design d;
  ASSERT_TRUE(d.Build(kLimitsOfThreeSrc));

  d.Annotate(SdfIncrement("(IOPATH A Z (() (-5) (2)))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 0u);
  EXPECT_EQ(pd->error_limit[0], 5u);
}

// An amount may be written as three members, each with its own sign. With the
// first member selected both amounts are the negative ones, so both limits come
// down.
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

// The middle member of the same two amounts is written without a minus sign, so
// selecting it raises both limits. A sign read off the value as a whole rather
// than off the selected member would have lowered them here.
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

// And the third member, whose amounts are negative again and larger than the
// first member's, so the same SDF text leaves the limits somewhere else again.
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

// Zero is where one transition's limit is held, not the whole path's. An
// earlier entry leaves the rising and falling transitions holding different
// limits, and one amount then carries only the narrower one below zero.
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

// The delay half of an INCREMENT entry is decided separately from the two
// limits: the delay value adds to the path's delay while the empty pulse fields
// leave both limits where the declaration put them. Deriving the limits from
// the delay the entry just raised would have moved them to 46.
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

// ---------------------------------------------------------------------------
// PATHPULSE and PATHPULSEPERCENT annotate the pulse limits alone.
// ---------------------------------------------------------------------------

// A PATHPULSE construct states both limits outright and leaves the propagation
// delay it was measured against exactly where the module path declared it.
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

// The other construct of the pair states each limit as a percentage of the
// path's own delay, and leaves that delay alone just the same.
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

// Either construct may be written with one value instead of two, which sets
// both limits from the single value it states.
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

// The same single-value spelling of the percentage construct, where the one
// percentage stated scales the delay for both limits.
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

// ---------------------------------------------------------------------------
// A pulse limit a PATHPULSE construct sets above the delay behaves as one set
// equal to the delay.
// ---------------------------------------------------------------------------

// Both limits are written above the path's delay, and the path behaves as
// though both had been written at the delay.
TEST(SdfPulseLimitAnnotation, PathpulseLimitsAboveTheDelayBehaveAsTheDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (50) (90))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 40u);
  EXPECT_EQ(pd->error_limit[0], 40u);
}

// Only a limit above the delay is affected: the reject limit written below it
// stays at the value the construct wrote, so the rule is a ceiling rather than
// a reset of the whole construct.
TEST(SdfPulseLimitAnnotation, PathpulseLeavesALimitBelowTheDelayAlone) {
  Design d;
  ASSERT_TRUE(d.Build(kPlainPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (20) (90))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 20u);
  EXPECT_EQ(pd->error_limit[0], 40u);
}

// The delay a limit is measured against is the delay of its own transition. On
// a path whose rise and fall delays differ, one PATHPULSE construct lands
// above the delay in one slot and below it in the other, and each slot answers
// for itself.
TEST(SdfPulseLimitAnnotation, PathpulseMeasuresEachSlotAgainstItsOwnDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kRiseFallPathSrc));
  ASSERT_NE(d.Path(), nullptr);
  ASSERT_EQ(d.Path()->delays[0], 20u);
  ASSERT_EQ(d.Path()->delays[1], 80u);

  d.Annotate(SdfAbsolute("(PATHPULSE A Z (50) (60))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 20u);
  EXPECT_EQ(pd->error_limit[0], 20u);
  EXPECT_EQ(pd->reject_limit[1], 50u);
  EXPECT_EQ(pd->error_limit[1], 60u);
}

// The percentage spelling reaches above the delay when a percentage above 100
// is stated, and the same rule brings both limits back to the delay.
TEST(SdfPulseLimitAnnotation, PathpulsepercentOverAHundredBehavesAsTheDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kFiftyDelayPathSrc));

  d.Annotate(SdfAbsolute("(PATHPULSEPERCENT A Z (120) (150))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 50u);
  EXPECT_EQ(pd->error_limit[0], 50u);
}

// ---------------------------------------------------------------------------
// The limit-only constructs obey the mode of the section carrying them, so in
// INCREMENT mode their values change the limits in place and the same two
// floors -- zero below, the path's delay above -- decide where a change stops.
// ---------------------------------------------------------------------------

// The subtracting case: each value comes off the limit the declaration put in
// place rather than replacing it.
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

// The floor at zero reaches this construct too: amounts larger than the limits
// they come off leave both at zero rather than below it.
TEST(SdfPulseLimitAnnotation, PathpulseIncrementBelowZeroLeavesLimitsAtZero) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(PATHPULSE A Z (-25) (-40))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 0u);
  EXPECT_EQ(pd->error_limit[0], 0u);
}

// The single-value spelling changes both limits by the one amount it states,
// the same way that spelling sets both limits when it states them outright.
TEST(SdfPulseLimitAnnotation, PathpulseIncrementWithOneValueMovesBothLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(PATHPULSE A Z (5))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 26u);
  EXPECT_EQ(pd->error_limit[0], 39u);
}

// A change that would carry a limit past the path's delay lands where a limit
// set at the delay would: the amounts here reach 51 and 64 against a delay of
// 40.
TEST(SdfPulseLimitAnnotation,
     PathpulseIncrementAboveTheDelayBehavesAsTheDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kPathWithLimitsSrc));

  d.Annotate(SdfIncrement("(PATHPULSE A Z (30) (30))"));

  const auto* pd = d.Path();
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 40u);
  EXPECT_EQ(pd->error_limit[0], 40u);
}

// A percentage stays a share of the path's delay when it states a change, so
// what it adds is that share rather than the number itself: 10% of a delay of
// 50 raises each limit the earlier construct left by 5.
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
