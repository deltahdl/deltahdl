#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.12 forbids nested disable iff clauses.
TEST(PropertyDeclarationElaboration, ExplicitDisableIffNestingRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property bad;\n"
      "    @(posedge clk) disable iff (r1) disable iff (r2) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12 forbids disable iff nesting that arises through property
// instantiation: one disable iff in the outer body plus one inside an
// instantiated callee makes two in the flattened form.
TEST(PropertyDeclarationElaboration,
     DisableIffNestingViaInstantiationRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12 permits exactly one disable iff in a property_spec.
TEST(PropertyDeclarationElaboration, SingleDisableIffNotFlaggedAsNested) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property ok;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12: the no-nesting rule sees disable iff clauses that accumulate across a
// multi-level instantiation chain. root carries one and the transitively
// instantiated leaf carries another, with an intermediate property between
// them; the flattened form has two, so it is rejected.
TEST(PropertyDeclarationElaboration,
     DisableIffNestingViaChainedInstantiationRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property mid;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) mid();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12: two sibling instantiations each contribute a disable iff to the same
// flattened property even though the instantiating property has none of its
// own. Their counts add to two, so the enclosing property is rejected.
TEST(PropertyDeclarationElaboration,
     TwoSiblingDisableIffLeavesUnderOneRootRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property l1;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property l2;\n"
      "    @(posedge clk) disable iff (r2) c |-> d;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) l1() and l2();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12: the count is per flattened property, not per module. Two unrelated
// properties that each carry exactly one disable iff and do not instantiate one
// another are both legal.
TEST(PropertyDeclarationElaboration,
     IndependentSingleDisableIffPropertiesAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    @(posedge clk) disable iff (r2) c |-> d;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12: a single disable iff that reaches a property purely through one
// instantiation (the instantiating property has none of its own) flattens to a
// count of one and is accepted.
TEST(PropertyDeclarationElaboration, SingleDisableIffViaInstantiationAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12 head: a sampled value function other than $sampled used in a disable
// condition requires an explicit clock argument; $sampled does not.
TEST(PropertyDeclarationElaboration, DisableConditionSampledValueNeedsClock) {
  // $sampled is well-formed with or without an explicit clock.
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, /*clock_explicitly_specified=*/false));
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, /*clock_explicitly_specified=*/true));
  EXPECT_FALSE(DisableConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kSampled));

  // Every value-change / past function needs the clock named explicitly.
  for (SampledValueFunction fn :
       {SampledValueFunction::kRose, SampledValueFunction::kFell,
        SampledValueFunction::kStable, SampledValueFunction::kChanged,
        SampledValueFunction::kPast}) {
    EXPECT_TRUE(DisableConditionSampledValueRequiresExplicitClock(fn));
    EXPECT_FALSE(DisableConditionSampledValueClockIsWellFormed(
        fn, /*clock_explicitly_specified=*/false));
    EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
        fn, /*clock_explicitly_specified=*/true));
  }
}

// §16.12 + §F.4.1: arity mismatch makes the flattened form not legal.
TEST(PropertyDeclarationElaboration, FlattenRejectsArgCountMismatch) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"a", "b"};
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 1);
  EXPECT_FALSE(fp.legal);
}

// §16.12 + §F.4.1: a well-formed flatten is acceptable as a top-level spec.
TEST(PropertyDeclarationElaboration, FlattenAcceptsWellFormedProperty) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"x"};
  decl.prop_disable_iff_count = 1;
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 1);
  EXPECT_TRUE(fp.legal);
  EXPECT_EQ(fp.disable_iff_count, 1);
  EXPECT_TRUE(PropertyRegistry::IsAcceptableAsTopLevelConcurrent(fp));
}

}  // namespace
