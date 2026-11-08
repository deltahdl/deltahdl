#include <gtest/gtest.h>

#include "elaborator/clock_resolution.h"
#include "elaborator/rtlir.h"
#include "elaborator/semantic_leading_clock.h"
#include "fixture_elaborator.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ClockResolution, ExplicitClockWinsOverInferredAndDefault) {
  auto r = ResolveConcurrentAssertionClock("posedge ex", "posedge inf",
                                           "posedge def");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kExplicit);
  EXPECT_EQ(r.event, "posedge ex");
}

TEST(ClockResolution, ExplicitClockWinsOverInferredWithoutDefault) {
  auto r = ResolveConcurrentAssertionClock("posedge ex", "posedge inf", "");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kExplicit);
  EXPECT_EQ(r.event, "posedge ex");
}

TEST(ClockResolution, ExplicitAssertionClockSupersedesDefaultClocking) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, clk;\n"
      "  default clocking dc @(negedge clk);\n"
      "  endclocking\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];
  bool clocked_on_explicit = false;
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF && p.sensitivity.size() == 1 &&
        p.sensitivity[0].edge == Edge::kPosedge &&
        p.sensitivity[0].signal != nullptr &&
        p.sensitivity[0].signal->text == "clk") {
      clocked_on_explicit = true;
    }
  }
  EXPECT_TRUE(clocked_on_explicit);
}

TEST(ClockResolution, InferredClockSupersedesDefault) {
  auto r = ResolveConcurrentAssertionClock("", "posedge inf", "posedge def");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kInferred);
  EXPECT_EQ(r.event, "posedge inf");
}

TEST(ClockResolution, InferredClockUsedWithoutDefault) {
  auto r = ResolveConcurrentAssertionClock("", "posedge inf", "");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kInferred);
  EXPECT_EQ(r.event, "posedge inf");
}

TEST(ClockResolution, DefaultClockUsedWhenNothingElseApplies) {
  auto r = ResolveConcurrentAssertionClock("", "", "posedge def");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kDefault);
  EXPECT_EQ(r.event, "posedge def");
}

TEST(ClockResolution, NoClockWhenNoneSpecified) {
  auto r = ResolveConcurrentAssertionClock("", "", "");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kNone);
  EXPECT_TRUE(r.event.empty());
}

TEST(ClockResolution,
     DefaultClockReachesDeclarationOnlyInDefaultClockingBlock) {
  EXPECT_TRUE(DefaultClockAppliesToDeclaration(true));
  EXPECT_FALSE(DefaultClockAppliesToDeclaration(false));
}

TEST(ClockResolution, ClockingBlockDeclarationInheritsBlockClock) {
  EXPECT_EQ(ClockingBlockDeclarationLeadingClock("posedge clk"), "posedge clk");
}

TEST(ClockResolution, ExternalInstanceInClockingBlockMustMatchBlockClock) {
  EXPECT_TRUE(ClockingBlockExternalInstanceIsLegal(false, "posedge clk",
                                                   "posedge clk"));
  EXPECT_FALSE(ClockingBlockExternalInstanceIsLegal(false, "negedge clk",
                                                    "posedge clk"));
  EXPECT_FALSE(
      ClockingBlockExternalInstanceIsLegal(true, "posedge clk", "posedge clk"));
}

TEST(ClockResolution, MulticlockedMaximalPropertyNeedsUniqueLeadingClock) {
  LeadingClockSet unique{std::string{"posedge clk"}};
  EXPECT_TRUE(MulticlockedMaximalPropertyIsLegal(unique));

  LeadingClockSet ambiguous{std::string{"posedge clk1"},
                            std::string{"posedge clk2"}};
  EXPECT_FALSE(MulticlockedMaximalPropertyIsLegal(ambiguous));

  LeadingClockSet inherited{std::string{InheritedSentinel()}};
  EXPECT_FALSE(MulticlockedMaximalPropertyIsLegal(inherited));

  LeadingClockSet empty;
  EXPECT_FALSE(MulticlockedMaximalPropertyIsLegal(empty));
}

TEST(ClockResolution, UnclockedAssertionLegalOnlyWithUniquelyClockedInstance) {
  EXPECT_TRUE(UnclockedAssertionIsLegal(true, true));
  EXPECT_FALSE(UnclockedAssertionIsLegal(true, false));
  EXPECT_FALSE(UnclockedAssertionIsLegal(false, true));
}

}  // namespace
