#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

ModuleItem* FindInstantiation(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

TEST(InterfaceInstantiationGrammar, BasicInterfaceInstantiation) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindInstantiation(r.cu->modules[0]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "ifc");
  EXPECT_EQ(inst->inst_name, "u0");
  EXPECT_EQ(inst->inst_params.size(), 0u);
}

TEST(InterfaceInstantiationGrammar, WithParameterValueAssignment) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc #(8) u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindInstantiation(r.cu->modules[0]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "ifc");
  EXPECT_EQ(inst->inst_params.size(), 1u);
}

TEST(InterfaceInstantiationGrammar, MultipleHierarchicalInstances) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0(), u1(), u2();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  VerifyHierarchicalInstanceList(r.cu->modules[0]->items, "ifc",
                                 {"u0", "u1", "u2"});
}

TEST(InterfaceInstantiationGrammar, MultipleInstancesShareParameters) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc #(16) u0(), u1();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i1->inst_params.size(), 1u);
}

TEST(InterfaceInstantiationGrammar, ErrorMissingSemicolon) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0()\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 4, "23.3.2"));
}

TEST(InterfaceInstantiationGrammar, ErrorTrailingCommaInInstanceList) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0(), ;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 3, "23.3.2"));
}

TEST(InterfaceInstantiationGrammar, InstanceNameDimensionAndWildcard) {
  auto r = Parse(
      "interface ifc(input logic clk); endinterface\n"
      "module m(input logic clk);\n"
      "  ifc \\b.0 (.*);\n"
      "  ifc bs[0:3] (clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->inst_name, "b.0");
  EXPECT_TRUE(items[0]->inst_wildcard);
  EXPECT_EQ(items[1]->inst_name, "bs");
  EXPECT_NE(items[1]->inst_range_left, nullptr);
  EXPECT_NE(items[1]->inst_range_right, nullptr);
}

TEST(InterfaceInstantiationGrammar, ParameterValueForms) {
  auto r = Parse(
      "interface ifc #(parameter int W = 8, parameter type T = logic);\n"
      "endinterface\n"
      "module m;\n"
      "  ifc #(1:2:3, bit) u0();\n"
      "  ifc #(.W($), .T(int)) u1();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  ASSERT_EQ(items[0]->inst_params.size(), 2u);
  EXPECT_EQ(items[0]->inst_params[0].second->kind, ExprKind::kMinTypMax);
  ASSERT_EQ(items[1]->inst_params.size(), 2u);
  EXPECT_EQ(items[1]->inst_params[0].first, "W");
  EXPECT_EQ(items[1]->inst_params[1].first, "T");
}

TEST(InterfaceInstantiationGrammar, InstantiatedInsideInterfaceAndGenerate) {
  auto r = Parse(
      "interface leaf; endinterface\n"
      "interface bus;\n"
      "  leaf l0();\n"
      "  if (1) begin : g\n"
      "    leaf l1();\n"
      "  end\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 2u);
  auto* inst = FindInstantiation(r.cu->interfaces[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "leaf");
  EXPECT_EQ(inst->inst_name, "l0");
}

}  // namespace
