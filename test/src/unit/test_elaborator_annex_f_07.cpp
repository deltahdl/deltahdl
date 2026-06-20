#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"

using namespace delta;

// §F.7 Recursive properties.
//
// §F.7 gives the precise versions of the four restrictions stated informally in
// §16.12.17, founded on the dependency digraph: the vertices are the named
// properties, and there is an edge (p, q) iff an instance of q appears in the
// declaration of p. A named property is recursive iff it lies in a nontrivial
// strongly connected component of that digraph (i.e. it can be reached from
// itself). The elaborator's PropertyRegistry builds exactly this digraph, and
// the same restriction checks are shared with §16.12.17.

namespace {

// §F.7: in the worked digraph <{p1,p2,p3},{(p1,p2),(p1,p3),(p3,p1)}> the
// nontrivial strongly connected component is {p1, p3}; p2 is reached but is not
// on a cycle. So p1 and p3 are recursive while p2 is not.
TEST(RecursivePropertyDependencyDigraph,
     RecursiveIffInStronglyConnectedComponent) {
  PropertyRegistry reg;
  ModuleItem p1;
  p1.kind = ModuleItemKind::kPropertyDecl;
  p1.name = "p1";
  p1.prop_instance_refs = {"p2", "p3"};
  ModuleItem p2;
  p2.kind = ModuleItemKind::kPropertyDecl;
  p2.name = "p2";
  // p2's body has no property instance.
  ModuleItem p3;
  p3.kind = ModuleItemKind::kPropertyDecl;
  p3.name = "p3";
  p3.prop_instance_refs = {"p1"};
  reg.Register(&p1);
  reg.Register(&p2);
  reg.Register(&p3);

  EXPECT_TRUE(reg.IsRecursiveProperty(&p1));
  EXPECT_TRUE(reg.IsRecursiveProperty(&p3));
  EXPECT_FALSE(reg.IsRecursiveProperty(&p2));
}

// §F.7: a recursive property can be *reached* from properties that are not
// themselves recursive. RESTRICTION 1 is phrased over this reachability — "a
// property from which a recursive property can be reached".
TEST(RecursivePropertyDependencyDigraph,
     ReachabilityToRecursivePropertyIsTransitive) {
  PropertyRegistry reg;
  ModuleItem rec;
  rec.kind = ModuleItemKind::kPropertyDecl;
  rec.name = "rec";
  rec.prop_instance_refs = {"rec"};
  ModuleItem mid;
  mid.kind = ModuleItemKind::kPropertyDecl;
  mid.name = "mid";
  mid.prop_instance_refs = {"rec"};
  ModuleItem unrelated;
  unrelated.kind = ModuleItemKind::kPropertyDecl;
  unrelated.name = "unrelated";
  reg.Register(&rec);
  reg.Register(&mid);
  reg.Register(&unrelated);

  EXPECT_FALSE(reg.IsRecursiveProperty(&mid));
  EXPECT_TRUE(reg.ReachesRecursiveProperty(&mid));
  EXPECT_FALSE(reg.ReachesRecursiveProperty(&unrelated));
}

// §F.7 RESTRICTION 1: not cannot be applied to a property expression that
// instantiates a property from which a recursive property can be reached. Here
// `bad` negates `mid`, which is not itself recursive but reaches the recursive
// `rec` — so the negation is illegal.
TEST(RecursivePropertyRestrictionEnforcement,
     NotOnPropertyReachingRecursiveRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property mid(p);\n"
      "    rec(p);\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    not mid(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §F.7 RESTRICTION 2: disable iff cannot be used in the declaration of a
// recursive property.
TEST(RecursivePropertyRestrictionEnforcement,
     DisableIffInRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    disable iff (rst)\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §F.7 RESTRICTION 3: in every cycle of the dependency digraph the sum of the
// edge weights shall be positive. A self-loop whose single instance carries no
// time advance has weight zero and is rejected.
TEST(RecursivePropertyRestrictionEnforcement, ZeroWeightSelfCycleRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |-> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §F.7 RESTRICTION 3 (boundary): the same self-cycle is legal once the instance
// carries a positive advance (|=> contributes weight one to the cycle).
TEST(RecursivePropertyRestrictionEnforcement, PositiveWeightSelfCycleAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §F.7 RESTRICTION 4: for a recursive instance of q in p, each actual argument
// must be a formal of p, mention no formal of p, or bind to a local variable
// formal of q. Passing an expression over p's formals to a non-local formal is
// illegal.
TEST(RecursivePropertyRestrictionEnforcement,
     RecursiveArgumentToNonLocalFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property fib (int a, b, n, fib_sig);\n"
      "    (n > 0) |->\n"
      "    ((fib_sig == a) and (1'b1 |=> fib(b, a + b, n - 1, fib_sig)));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
