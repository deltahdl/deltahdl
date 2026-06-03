#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"

using namespace delta;

// §16.12.17 Recursive properties.
//
// A named property is recursive if its declaration involves an instantiation of
// itself (directly, or through mutual recursion). The elaborator enforces the
// four restrictions the subclause places on recursive property declarations:
//   Restriction 1: not / the strong operators may not be applied to a property
//     expression that instantiates (reaches) a recursive property.
//   Restriction 2: disable iff may not appear in a recursive property.
//   Restriction 3: every recursive instance must occur after a positive time
//     advance.
//   Restriction 4: the actual arguments of a recursive instance are limited.
// The accept_on / reject_on family, by contrast, may be used freely inside a
// recursive property.

namespace {

// §16.12.17: recursion is detected from the property-to-property dependency
// digraph. A property that instantiates itself is recursive; one that only
// instantiates another property once is not.
TEST(RecursivePropertyDetection, SelfInstantiationIsRecursiveSingleCallIsNot) {
  PropertyRegistry reg;
  ModuleItem rec;
  rec.kind = ModuleItemKind::kPropertyDecl;
  rec.name = "prop_always";
  rec.prop_instance_refs = {"prop_always"};
  ModuleItem caller;
  caller.kind = ModuleItemKind::kPropertyDecl;
  caller.name = "p1";
  caller.prop_instance_refs = {"prop_always"};
  reg.Register(&rec);
  reg.Register(&caller);

  EXPECT_TRUE(reg.IsRecursiveProperty(&rec));
  EXPECT_FALSE(reg.IsRecursiveProperty(&caller));
  // p1 is not recursive, but a recursive property is reachable from it.
  EXPECT_TRUE(reg.ReachesRecursiveProperty(&caller));
  EXPECT_TRUE(reg.ReachesRecursiveProperty(&rec));
}

// §16.12.17: "several properties can be mutually recursive" — each property in
// the cycle reaches itself through the other.
TEST(RecursivePropertyDetection, MutuallyRecursivePropertiesAreRecursive) {
  PropertyRegistry reg;
  ModuleItem a;
  a.kind = ModuleItemKind::kPropertyDecl;
  a.name = "check_phase1";
  a.prop_instance_refs = {"check_phase2"};
  ModuleItem b;
  b.kind = ModuleItemKind::kPropertyDecl;
  b.name = "check_phase2";
  b.prop_instance_refs = {"check_phase1"};
  reg.Register(&a);
  reg.Register(&b);

  EXPECT_TRUE(reg.IsRecursiveProperty(&a));
  EXPECT_TRUE(reg.IsRecursiveProperty(&b));
}

// §16.12.17: a legal recursive property — the self-instance sits after a |=>
// time advance, there is no disable iff, no negation, and the actual argument
// is itself a formal. None of the four restrictions is violated.
TEST(RecursivePropertyRestrictions, WellFormedRecursivePropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property prop_always(p);\n"
      "    p and (1'b1 |=> prop_always(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.17 Restriction 1: applying not to a property expression that
// instantiates a recursive property is illegal (illegal_recursion_1).
TEST(RecursivePropertyRestrictions, NotAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property prop_always(p);\n"
      "    p and (1'b1 |=> prop_always(p));\n"
      "  endproperty\n"
      "  property illegal_recursion_1(p);\n"
      "    not prop_always(not p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.17 Restriction 1: a recursive property may negate its self-instance
// only if it were not recursive — illegal_recursion_2 negates its own instance.
TEST(RecursivePropertyRestrictions, NotAppliedToSelfInstanceRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property illegal_recursion_2(p);\n"
      "    p and (1'b1 |=> not illegal_recursion_2(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.17 Restriction 1: alongside not, the strong operators (s_nexttime,
// s_eventually, s_always, s_until, s_until_with) likewise cannot be applied to
// a property expression that instantiates a recursive property. Here
// s_eventually is applied to the recursive rec.
TEST(RecursivePropertyRestrictions, StrongOperatorAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    s_eventually rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.17 Restriction 1 (boundary): negating a plain, non-recursive property
// instance is perfectly legal.
TEST(RecursivePropertyRestrictions, NotAppliedToNonRecursivePropertyAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property leaf(p);\n"
      "    p |-> 1'b1;\n"
      "  endproperty\n"
      "  property user(p);\n"
      "    not leaf(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.17 Restriction 1 (edge): the negated property expression may be
// wrapped in parentheses. not applied to (rec(...)) still reaches the recursive
// rec and is illegal.
TEST(RecursivePropertyRestrictions, NotThroughParenthesesOnRecursiveRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    not (rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.17 Restriction 2: disable iff cannot be used in the declaration of a
// recursive property (illegal_recursion_3).
TEST(RecursivePropertyRestrictions, DisableIffInRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property illegal_recursion_3(p);\n"
      "    disable iff (b)\n"
      "    p and (1'b1 |=> illegal_recursion_3(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.17 Restriction 2 (boundary): the same disable iff is legal once the
// property is not recursive — legal_3 wraps the recursive prop_always but is
// not itself recursive.
TEST(RecursivePropertyRestrictions, DisableIffInNonRecursivePropertyAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property prop_always(p);\n"
      "    p and (1'b1 |=> prop_always(p));\n"
      "  endproperty\n"
      "  property legal_3(p);\n"
      "    disable iff (b) prop_always(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.17 Restriction 3: a self-instance reached with no positive advance in
// time (here through |->) leaves the recursion stuck at one cycle and is
// illegal (illegal_recursion_4).
TEST(RecursivePropertyRestrictions, SelfInstanceWithoutTimeAdvanceRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property illegal_recursion_4(p);\n"
      "    p and (1'b1 |-> illegal_recursion_4(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.17 Restriction 3 (edge): a cycle delay (##1) is also a positive
// advance in time, so a self-instance reached after ##1 satisfies the
// restriction even without |=>.
TEST(RecursivePropertyRestrictions, SelfInstanceAfterCycleDelayAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p ##1 rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.17 Restriction 4: each actual argument of a recursive instance must be
// a formal, contain no formal, or be bound to a local variable formal of the
// callee. fibonacci1 (all four formals local) satisfies this and is legal.
TEST(RecursivePropertyRestrictions, RecursiveArgsBoundToLocalFormalsAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property fibonacci1 (local input int a, b, n, int fib_sig);\n"
      "    (n > 0) |->\n"
      "    ((fib_sig == a) and (1'b1 |=> fibonacci1(b, a + b, n - 1, fib_sig)));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.17 Restriction 4: fibonacci2 passes a+b and n-1 — expressions that
// mention formals of fibonacci2 — to non-local formals, so it is illegal.
TEST(RecursivePropertyRestrictions, RecursiveArgsNotBoundToLocalFormalsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property fibonacci2 (int a, b, n, fib_sig);\n"
      "    (n > 0) |->\n"
      "    ((fib_sig == a) and (1'b1 |=> fibonacci2(b, a + b, n - 1, fib_sig)));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.17 Restriction 4 (edge): condition (b) — an actual argument that
// mentions no formal of the enclosing property (here the literal 5) is legal
// even when passed to a non-local formal of the recursive callee.
TEST(RecursivePropertyRestrictions, RecursiveArgWithNoEnclosingFormalAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property rec(p, n);\n"
      "    p and (1'b1 |=> rec(p, 5));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.17: the operators accept_on, reject_on, sync_accept_on, and
// sync_reject_on may be used inside a recursive property. The mutually
// recursive p3/p4 pair (p4 wraps its recursive call in accept_on/reject_on)
// elaborates cleanly.
TEST(RecursivePropertyRestrictions, AbortOperatorsAllowedInRecursiveProperty) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p3(p, bit b, abort);\n"
      "    (p and (1'b1 |=> p4(p, b, abort)));\n"
      "  endproperty\n"
      "  property p4(p, bit b, abort);\n"
      "    accept_on(b) reject_on(abort) p3(p, b, abort);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
