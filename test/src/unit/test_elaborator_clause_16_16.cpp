#include <gtest/gtest.h>

#include "elaborator/clock_resolution.h"
#include "elaborator/semantic_leading_clock.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.16(d): an explicitly specified leading clocking event wins over both a
// contextually inferred clock and a default clock.
TEST(ClockResolution, ExplicitClockWinsOverInferredAndDefault) {
  auto r = ResolveConcurrentAssertionClock("posedge ex", "posedge inf",
                                           "posedge def");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kExplicit);
  EXPECT_EQ(r.event, "posedge ex");
}

// §16.16(d): an explicit leading clocking event supersedes a contextually
// inferred one even when no default clocking event is in scope, so the
// explicit-over-inferred precedence boundary holds on its own.
TEST(ClockResolution, ExplicitClockWinsOverInferredWithoutDefault) {
  auto r = ResolveConcurrentAssertionClock("posedge ex", "posedge inf", "");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kExplicit);
  EXPECT_EQ(r.event, "posedge ex");
}

// §16.16(d): the same precedence applied by production, end to end. A module
// declares a default clocking on negedge clk and a concurrent assertion that
// carries its own explicit @(posedge clk). After parsing and elaboration the
// assertion is lowered to a clocked process whose sensitivity is the explicit
// posedge clk -- the default clocking event does not govern it -- so the
// explicit leading clock supersedes the default. The default clocking and the
// assertion are built from real §14.12/§16.14 source syntax and driven through
// the full pipeline rather than modeled by hand.
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
  // The assertion's clocked process is sensitive to the explicit posedge clk,
  // not the default's negedge -- evidence the explicit event was chosen.
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

// §16.16(c): a contextually inferred clocking event from a procedural block
// supersedes the default clocking event.
TEST(ClockResolution, InferredClockSupersedesDefault) {
  auto r = ResolveConcurrentAssertionClock("", "posedge inf", "posedge def");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kInferred);
  EXPECT_EQ(r.event, "posedge inf");
}

// §16.16(c): a contextually inferred clocking event becomes the leading clock
// even when no default clocking event is in scope.
TEST(ClockResolution, InferredClockUsedWithoutDefault) {
  auto r = ResolveConcurrentAssertionClock("", "posedge inf", "");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kInferred);
  EXPECT_EQ(r.event, "posedge inf");
}

// §16.16(a): with neither an explicit nor an inferred clock, the default
// clocking event becomes the leading clock of the assertion.
TEST(ClockResolution, DefaultClockUsedWhenNothingElseApplies) {
  auto r = ResolveConcurrentAssertionClock("", "", "posedge def");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kDefault);
  EXPECT_EQ(r.event, "posedge def");
}

// §16.16(f): when no explicit, inferred, or default clock applies the
// resolution yields no leading clock and the assertion's legality then
// depends on its maximal property.
TEST(ClockResolution, NoClockWhenNoneSpecified) {
  auto r = ResolveConcurrentAssertionClock("", "", "");
  EXPECT_EQ(r.origin, LeadingClockOrigin::kNone);
  EXPECT_TRUE(r.event.empty());
}

// §16.16(a): the default clocking event governs a sequence or property
// declaration only when that declaration sits in a clocking block whose
// clocking event is the default.
TEST(ClockResolution,
     DefaultClockReachesDeclarationOnlyInDefaultClockingBlock) {
  EXPECT_TRUE(DefaultClockAppliesToDeclaration(true));
  EXPECT_FALSE(DefaultClockAppliesToDeclaration(false));
}

// §16.16(b1): such a declaration takes the clocking block's event as its
// leading clocking event.
TEST(ClockResolution, ClockingBlockDeclarationInheritsBlockClock) {
  EXPECT_EQ(ClockingBlockDeclarationLeadingClock("posedge clk"), "posedge clk");
}

// §16.16(b3): a sequence/property declared outside a clocking block but
// instantiated inside one must be singly clocked with an event identical to
// the block's.
TEST(ClockResolution, ExternalInstanceInClockingBlockMustMatchBlockClock) {
  EXPECT_TRUE(ClockingBlockExternalInstanceIsLegal(
      /*instance_is_multiclocked=*/false, "posedge clk", "posedge clk"));
  // Differing clock is illegal.
  EXPECT_FALSE(ClockingBlockExternalInstanceIsLegal(
      /*instance_is_multiclocked=*/false, "negedge clk", "posedge clk"));
  // A multiclocked instance is illegal regardless of clock text.
  EXPECT_FALSE(ClockingBlockExternalInstanceIsLegal(
      /*instance_is_multiclocked=*/true, "posedge clk", "posedge clk"));
}

// §16.16(e): a multiclocked maximal property of a concurrent assertion is
// legal only if it has a unique semantic leading clock (§16.16.1).
TEST(ClockResolution, MulticlockedMaximalPropertyNeedsUniqueLeadingClock) {
  LeadingClockSet unique{std::string{"posedge clk"}};
  EXPECT_TRUE(MulticlockedMaximalPropertyIsLegal(unique));

  LeadingClockSet ambiguous{std::string{"posedge clk1"},
                            std::string{"posedge clk2"}};
  EXPECT_FALSE(MulticlockedMaximalPropertyIsLegal(ambiguous));

  // An inherited-only set has no usable clock and is rejected.
  LeadingClockSet inherited{std::string{InheritedSentinel()}};
  EXPECT_FALSE(MulticlockedMaximalPropertyIsLegal(inherited));

  // An empty clock set is not a unique leading clock and is rejected.
  LeadingClockSet empty;
  EXPECT_FALSE(MulticlockedMaximalPropertyIsLegal(empty));
}

// §16.16(f): an assertion with no explicit, inferred, or default leading clock
// is legal only when its maximal property is an instance of a sequence or
// property for which a unique leading clocking event is determined.
TEST(ClockResolution, UnclockedAssertionLegalOnlyWithUniquelyClockedInstance) {
  EXPECT_TRUE(
      UnclockedAssertionIsLegal(/*maximal_property_is_instance=*/true,
                                /*instance_has_unique_leading_clock=*/true));
  // Instance whose leading clock is not unique -> illegal.
  EXPECT_FALSE(
      UnclockedAssertionIsLegal(/*maximal_property_is_instance=*/true,
                                /*instance_has_unique_leading_clock=*/false));
  // Maximal property that is not an instance at all -> illegal.
  EXPECT_FALSE(
      UnclockedAssertionIsLegal(/*maximal_property_is_instance=*/false,
                                /*instance_has_unique_leading_clock=*/true));
}

}  // namespace
