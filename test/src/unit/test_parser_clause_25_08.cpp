#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParameterizedInterface, WithParameters) {
  auto r = Parse(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->params.empty());
}

TEST(ParameterizedInterface, WithConstants) {
  auto r = Parse(
      "interface ifc;\n"
      "  localparam int DEPTH = 16;\n"
      "  parameter int WIDTH = 8;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(
      CountItemsByKind(r.cu->interfaces[0]->items, ModuleItemKind::kParamDecl),
      1u);
}

TEST(ParameterizedInterface, InterfaceInstWithParams) {
  auto r = Parse("module m; my_if #(8) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

TEST(ParameterizedInterface, InterfaceInstWithNamedParams) {
  auto r = Parse("module m; my_if #(.W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

TEST(ParameterizedInterface, InterfaceInstEmptyParam) {
  auto r = Parse("module m; my_if #() u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_TRUE(item->inst_params.empty());
}

TEST(ParameterizedInterface, MultipleInstancesWithParams) {
  auto r = Parse(
      "module m; my_if #(.W(8)) u0(.a(a)), u1(.a(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_if");
  EXPECT_EQ(i0->inst_name, "u0");
  ASSERT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i0->inst_params[0].first, "W");
  EXPECT_EQ(i1->inst_module, "my_if");
  EXPECT_EQ(i1->inst_name, "u1");
}

TEST(ParameterizedInterface, MultipleParametersInHeader) {
  auto r = Parse(
      "interface ifc #(parameter int AWIDTH = 8, parameter int DWIDTH = 16);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->params[0].first, "AWIDTH");
  EXPECT_EQ(r.cu->interfaces[0]->params[1].first, "DWIDTH");
}

TEST(ParameterizedInterface, TypeParameterInHeader) {
  auto r = Parse(
      "interface ifc #(parameter type T = logic [7:0]);\n"
      "  T data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->params[0].first, "T");
}

TEST(ParameterizedInterface, ParameterUsedInInterfaceBody) {
  auto r = Parse(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 1u);
}

TEST(ParameterizedInterface, OverrideWithExpression) {
  auto r = Parse(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  my_if #(.W(N + 1)) u0(.a(a));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "W");
}

TEST(ParameterizedInterface, DuplicateNamedOverrideIsError) {
  auto r =
      Parse("module m; my_if #(.W(8), .W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(ParameterizedInterface, MixedOrderedAndNamedOverrideIsError) {
  auto r =
      Parse("module m; my_if #(8, .W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
