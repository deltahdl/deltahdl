#include <gtest/gtest.h>

#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(PropertyRewrite, UnknownNameNotLegal) {
  PropertyRegistry reg;
  auto fp = reg.Flatten("missing", 0);
  EXPECT_FALSE(fp.legal);
}

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

TEST(PropertyRewrite, FlattenedFormIllegalMakesSourceIllegalFromSource) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 5,
                            "16.12"));
}

TEST(PropertyRewrite, FlattenedFormLegalKeepsSourceLegalFromSource) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b, r2);\n"
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

TEST(PropertyRewrite,
     FlattenedFormNestsDisableIffThroughChainedInstancesFromSource) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

TEST(PropertyRewrite,
     FlattenedFormCollectsDisableIffFromSiblingInstancesFromSource) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2, c, d);\n"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

}  // namespace
