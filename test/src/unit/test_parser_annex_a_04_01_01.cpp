#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationGrammar, OrderedParameterAssignment) {
  auto r = Parse("module m; sub #(8, 4) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 2u);

  EXPECT_EQ(item->inst_params[0].first, "");
  EXPECT_EQ(item->inst_params[1].first, "");
}

TEST(ModuleInstantiationGrammar, NamedParameterAssignment) {
  auto r = Parse("module m; sub #(.WIDTH(8), .DEPTH(4)) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 2u);
  EXPECT_EQ(item->inst_params[0].first, "WIDTH");
  EXPECT_NE(item->inst_params[0].second, nullptr);
  EXPECT_EQ(item->inst_params[1].first, "DEPTH");
  EXPECT_NE(item->inst_params[1].second, nullptr);
}

TEST(ModuleInstantiationGrammar, NamedParameterEmptyExpression) {
  auto r = Parse("module m; sub #(.WIDTH()) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "WIDTH");
  EXPECT_EQ(item->inst_params[0].second, nullptr);
}

TEST(ModuleInstantiationGrammar, SingleOrderedParam) {
  auto r = Parse("module m; sub #(16) u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
}

TEST(ModuleInstantiationGrammar, InstanceArrayWithSize) {
  auto r = Parse("module m; sub u0[4](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_EQ(item->inst_range_right, nullptr);
}

TEST(ModuleInstantiationGrammar, EmptyPortList) {
  auto r = Parse("module m; sub u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_ports.size(), 0u);
}

TEST(ModuleInstantiationGrammar, NamedParamsAndNamedPorts) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.W(8), .D(4)) u0(.clk(clk), .data(d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 2u);
  EXPECT_EQ(item->inst_params[0].first, "W");
  EXPECT_EQ(item->inst_params[1].first, "D");
  EXPECT_EQ(item->inst_ports.size(), 2u);
}

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

TEST(ModuleInstantiationGrammar, InstanceArrayWithRangeAndPorts) {
  auto r = Parse(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [3:0] x, y;\n"
      "  sub u0[3:0](.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_name, "u0");
  EXPECT_NE(inst->inst_range_left, nullptr);
  EXPECT_NE(inst->inst_range_right, nullptr);
}

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

TEST(ModuleInstantiationGrammar, ParametersArrayAndWildcardCombined) {
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

TEST(ModuleInstantiationGrammar, SimpleInstanceNoConnections) {
  auto r = Parse(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[1]->items[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(ModuleInstantiationGrammar, MultipleLevelsOfHierarchy) {
  EXPECT_TRUE(
      ParseOk("module leaf; endmodule\n"
              "module mid; leaf u0(); endmodule\n"
              "module top; mid u0(); endmodule\n"));
}

TEST(ModuleInstantiationGrammar, AttributeOnPortConnection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sub u1(.a(x), (* no_connect *) .b(y));\n"
              "endmodule"));
}

TEST(ModuleInstantiationGrammar, TopMux2to1Example) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  not g1 (sel_n, sel);\n"
      "  and g2 (a_s, a, sel_n);\n"
      "  and g3 (b_s, b, sel);\n"
      "  or  g4 (y, a_s, b_s);\n"
      "endmodule: mux2to1\n"
      "module top;\n"
      "  logic in1, in2, select;\n"
      "  wire out1;\n"
      "  mux2to1 m1 (.a(in1), .b(in2), .sel(select), .y(out1));\n"
      "endmodule: top\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[1]->name, "top");
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

TEST(ModuleInstantiationGrammar, NamedPortWithoutParens) {
  auto r = Parse("module m; sub u0(.clk, .data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "data");
}

TEST(ModuleInstantiationGrammar, WildcardPortConnection) {
  auto r = Parse("module m; sub u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ModuleInstantiationGrammar, WildcardWithNamedPorts) {
  auto r = Parse("module m; sub u0(.clk(clk), .*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

TEST(ModuleInstantiationGrammar, ElaborationWildcardPortConnection) {
  auto r = Parse(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire a, b;\n"
      "  sub u0(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  EXPECT_EQ(inst->inst_ports.size(), 0u);
}

TEST(ModuleInstantiationGrammar, WildcardConnection) {
  auto r = Parse(
      "module top;\n"
      "  sub m1(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "m1");
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ModuleInstantiationGrammar, WildcardWithNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub m1(.*, .clk(sys_clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

TEST(ModuleInstantiationGrammar, WildcardOnly) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(ModuleInstantiationGrammar, WildcardWithNamedOverrides) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*, .rst(global_rst), .clk(sys_clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "rst");
  EXPECT_EQ(item->inst_ports[1].first, "clk");
}

TEST(ModuleInstantiationGrammar, WildcardWithEmptyPort) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*, .unused());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "unused");
  EXPECT_EQ(item->inst_ports[0].second, nullptr);
}

TEST(ModuleInstantiationGrammar, ModuleInstWithParams) {
  auto r = Parse("module m; sub #(8, 4) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 2u);
}

TEST(ModuleInstantiationGrammar, OrderedParamsNamedPorts) {
  auto r = Parse("module m; sub #(8) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "");
  EXPECT_EQ(item->inst_ports.size(), 1u);
}

TEST(ModuleInstantiationGrammar, OrderedParameterOverrideMultiModule) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(8) u0(.d(8'd0));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "");
  EXPECT_NE(inst->inst_params[0].second, nullptr);
}

TEST(ModuleInstantiationGrammar, ModuleInstanceWithParameters) {
  auto r = Parse(
      "module top;\n"
      "  sub #(8, 16) u1 (.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u1");
  ASSERT_EQ(item->inst_params.size(), 2);
}

TEST(ModuleInstantiationGrammar, NamedParameterOverrideMultiModule) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(16)) u0(.d(16'd0));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "W");
  EXPECT_NE(inst->inst_params[0].second, nullptr);
}

TEST(ModuleInstantiationGrammar, ModuleInstNamedParamOverride) {
  auto r = Parse(
      "module top;\n"
      "  sub #(.WIDTH(8), .DEPTH(16)) u1(.a(w1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
}

TEST(ModuleInstantiationGrammar, InstanceArrayWithRange) {
  auto r = Parse("module m; sub u0[3:0](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(ModuleInstantiationGrammar, InstanceArrayKind) {
  auto r = Parse(
      "module top;\n"
      "  sub inst[3:0] (.a(a), .b(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "inst");
}

TEST(ModuleInstantiationGrammar, AttributeOnWildcardPort) {
  auto r = Parse(
      "module m;\n"
      "  sub u0(.clk(clk), (* synthesis_off *) .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 1u);
}

TEST(ModuleInstantiationGrammar, ImplicitAndExplicitNamedPorts) {
  auto r = Parse("module m; sub u0(.a, .b(x), .c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_EQ(item->inst_ports[2].first, "c");
}


TEST(ModuleInstantiationGrammar, InstanceArrayMultipleDimensions) {
  auto r = Parse("module m; sub u0[3:0][7:0](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_dims.size(), 2u);
  EXPECT_NE(item->inst_dims[0].first, nullptr);
  EXPECT_NE(item->inst_dims[0].second, nullptr);
  EXPECT_NE(item->inst_dims[1].first, nullptr);
  EXPECT_NE(item->inst_dims[1].second, nullptr);
  EXPECT_EQ(item->inst_range_left, item->inst_dims[0].first);
  EXPECT_EQ(item->inst_range_right, item->inst_dims[0].second);
}

TEST(ModuleInstantiationGrammar, ErrorMissingInstanceName) {
  auto r = Parse("module m; sub(a, b); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstantiationGrammar, ErrorMissingPortParentheses) {
  auto r = Parse("module m; sub u0; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
