#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationGrammar, BasicModuleInst) {
  auto r = Parse("module m; sub u0(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ModuleInstantiationGrammar, MultipleHierarchicalInstances) {
  auto r = Parse("module m; sub u0(a), u1(b), u2(c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  auto* i2 = r.cu->modules[0]->items[2];
  EXPECT_EQ(i0->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(i0->inst_module, "sub");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(i1->inst_module, "sub");
  EXPECT_EQ(i1->inst_name, "u1");
  EXPECT_EQ(i2->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(i2->inst_module, "sub");
  EXPECT_EQ(i2->inst_name, "u2");
}

TEST(ModuleInstantiationGrammar, MultipleInstancesWithParams) {
  auto r = Parse("module m; sub #(8) u0(a), u1(b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "sub");
  EXPECT_EQ(i1->inst_module, "sub");
  EXPECT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i1->inst_params.size(), 1u);
}

TEST(ModuleInstantiationGrammar, EmptyParameterValueAssignment) {
  auto r = Parse("module m; sub #() u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 0u);
}

TEST(ModuleInstantiationGrammar, FullCombination) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.W(8)) u0[3:0](.clk(clk), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
  EXPECT_EQ(item->inst_ports.size(), 1u);
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ModuleInstantiationGrammar, MultipleInstancesSharedParams) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(8)) u0(.d(8'd0)), u1(.d(8'd1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[1]->items.size(), 2u);
  auto* i0 = r.cu->modules[1]->items[0];
  auto* i1 = r.cu->modules[1]->items[1];
  EXPECT_EQ(i0->inst_module, "sub");
  EXPECT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i0->inst_params[0].first, "W");
  EXPECT_EQ(i1->inst_module, "sub");
  EXPECT_EQ(i1->inst_params.size(), 1u);
  EXPECT_EQ(i1->inst_params[0].first, "W");
}

TEST(InterfaceInstantiationGrammar, InterfaceInstEmptyParam) {
  auto r = Parse("module m; my_if #() u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_TRUE(item->inst_params.empty());
}

TEST(ProgramInstantiationGrammar, ProgramInstEmptyParam) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog #() u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_TRUE(item->inst_params.empty());
}
TEST(ModuleAndHierarchyParsing, InstanceArraySingle) {
  auto r = Parse(
      "module top;\n"
      "  sub inst[8] (.a(a));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_name, "inst");
  EXPECT_NE(item->inst_range_left, nullptr);

  EXPECT_EQ(item->inst_range_right, nullptr);
}

TEST(ModuleAndHierarchyParsing, ModuleInstanceEmptyPorts) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_name, "u1");
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(ModuleInstantiation, SimpleInstanceNoConnections) {
  auto r = Parse(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[1]->items[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(ModuleInstantiation, ModuleInstantiatesModule) {
  auto r = Parse(
      "module sub; endmodule\n"
      "module top;\n"
      "  sub u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

TEST(ModuleInstantiation, MultipleLevelsOfHierarchy) {
  EXPECT_TRUE(
      ParseOk("module leaf; endmodule\n"
              "module mid; leaf u0(); endmodule\n"
              "module top; mid u0(); endmodule\n"));
}

}  // namespace
