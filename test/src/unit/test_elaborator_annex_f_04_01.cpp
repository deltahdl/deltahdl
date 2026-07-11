#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §F.4.1: if flattened is not legal, source is not legal — unknown names
// surface that as legal=false.
TEST(PropertyRewrite, UnknownNameNotLegal) {
  PropertyRegistry reg;
  auto fp = reg.Flatten("missing", 0);
  EXPECT_FALSE(fp.legal);
}

// §F.4.1: a rewritten property may be the top-level property of a
// concurrent assertion, and the flattened form has no remaining instances.
TEST(PropertyRewrite, LegalFlattenAcceptsAsTopLevel) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 0);
  EXPECT_TRUE(fp.legal);
  EXPECT_EQ(fp.remaining_instances, 0);
  EXPECT_TRUE(PropertyRegistry::IsAcceptableAsTopLevelConcurrent(fp));
}

// §F.4.1 step 2: actual count must bind every formal.
TEST(PropertyRewrite, ArgArityMismatchSurfacesAsNotLegal) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"a", "b", "c"};
  reg.Register(&decl);

  EXPECT_FALSE(reg.Flatten("p", 0).legal);
  EXPECT_FALSE(reg.Flatten("p", 2).legal);
  EXPECT_TRUE(reg.Flatten("p", 3).legal);
}

// §F.4.1 end-to-end: the rewriting algorithm flattens a hierarchical property
// by inlining its instances, and legality is judged on that flattened form.
// Here `leaf` and `root` each carry exactly one disable iff, so each is legal
// on its own; flattening `root` inlines `leaf`, coalescing the two disable iff
// clauses into a single flattened property that is not legal. Per §F.4.1, an
// illegal flattened form makes the source not legal, so elaboration of real
// source rejects `root`. Drives parse + elaborate against the wired
// FlattenedDisableIffCount so the rule is observed on production input.
TEST(PropertyRewrite, FlattenedFormIllegalMakesSourceIllegalFromSource) {
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

// §F.4.1 companion to the above, isolating the flattening step: the `root`
// declaration is byte-for-byte the same, but the inlined `leaf` now contributes
// no disable iff. The flattened form therefore holds a single disable iff and
// is legal, so the source stays legal and elaborates. Legality tracks the
// flattened form (§F.4.1), not any one declaration in isolation — the only
// change between this pair is what flattening pulls in from the instance.
TEST(PropertyRewrite, FlattenedFormLegalKeepsSourceLegalFromSource) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §F.4.1 (closing sentence): a property produced by the rewriting algorithm may
// serve as the top-level property of a concurrent assertion. `root` is
// hierarchical — it instantiates `leaf`, so it is exactly the kind of property
// the algorithm rewrites — and it is used directly as the top-level property of
// an `assert property`. The flattened form is a legal top-level property, so
// the concurrent assertion elaborates without error. Driven from real source
// through parse + elaborate rather than asserting the helper on a built state.
TEST(PropertyRewrite,
     HierarchicalPropertyServesAsTopLevelConcurrentFromSource) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "  assert property (root);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §F.4.1: the flattened form holds no instances, so the algorithm must inline
// transitively. `root` instantiates `mid`, which instantiates `leaf`; `root`
// and `leaf` each carry one disable iff while `mid` carries none. Only a
// transitive flattening reaches `leaf`'s disable iff, so the flattened `root`
// ends up with two — an illegal form that, per §F.4.1, makes the source
// illegal. This exercises the multi-level traversal that a single direct
// instance does not.
TEST(PropertyRewrite,
     FlattenedFormNestsDisableIffThroughChainedInstancesFromSource) {
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

// §F.4.1: flattening inlines every instance in a body, so disable iff clauses
// reached through distinct sibling instances coincide in one flattened form.
// `root` has none of its own but instantiates `l1` and `l2`, each carrying one;
// the flattened `root` therefore has two and is illegal, and the source with
// it. This exercises collection across multiple instances in one body, distinct
// from the single-instance and chained forms.
TEST(PropertyRewrite,
     FlattenedFormCollectsDisableIffFromSiblingInstancesFromSource) {
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

}  // namespace
