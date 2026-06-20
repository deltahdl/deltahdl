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
