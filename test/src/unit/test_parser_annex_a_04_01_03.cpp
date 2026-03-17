#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ProgramInstantiationGrammar, ProgramInstWithOrderedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(16) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

TEST(ProgramInstantiationGrammar, ProgramInstEmptyPorts) {
  auto r = Parse(
      "program my_prog;\n"
      "endprogram\n"
      "module m; my_prog u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(ProgramInstantiationGrammar, BasicProgramInst) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ProgramInstantiationGrammar, MultipleProgramInstances) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(a)), u1(.clk(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_prog");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_prog");
  EXPECT_EQ(i1->inst_name, "u1");
}

TEST(ProgramInstantiationGrammar, ProgramInstantiatedInModule) {
  auto r = Parse(
      "program test_prog(input logic clk);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk;\n"
      "  test_prog tp(.clk(clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const auto* inst =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "test_prog");
  EXPECT_EQ(inst->inst_name, "tp");
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

TEST(ProgramInstantiationGrammar, ProgramInstOrderedPorts) {
  auto r = Parse(
      "program my_prog(input logic a, input logic b, input logic c);\n"
      "endprogram\n"
      "module m; my_prog u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

TEST(ProgramInstantiationGrammar, ProgramInstNamedPortNoParens) {
  auto r = Parse(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

TEST(ProgramInstantiationGrammar, ProgramInstWildcardPort) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ProgramInstantiationGrammar, ProgramInstWithNamedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(.W(16)) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

TEST(ProgramInstantiationGrammar, ProgramInstArray) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0 [3:0] (.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(ProgramInstantiationGrammar, MultipleInstancesWithParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(.W(8)) u0(.data(a)), u1(.data(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_prog");
  EXPECT_EQ(i0->inst_name, "u0");
  ASSERT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i0->inst_params[0].first, "W");
  EXPECT_EQ(i1->inst_module, "my_prog");
  EXPECT_EQ(i1->inst_name, "u1");
}

TEST(ProgramInstantiationGrammar, ThreeCommaSeparatedInstances) {
  auto r = Parse(
      "program my_prog;\n"
      "endprogram\n"
      "module m; my_prog u0(), u1(), u2(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->inst_name, "u0");
  EXPECT_EQ(r.cu->modules[0]->items[1]->inst_name, "u1");
  EXPECT_EQ(r.cu->modules[0]->items[2]->inst_name, "u2");
}

TEST(ProgramInstantiationGrammar, ParamsWithEmptyPorts) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8);\n"
      "endprogram\n"
      "module m; my_prog #(8) u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(ProgramInstantiationGrammar, Error_MissingSemicolon) {
  EXPECT_FALSE(ParseOk(
      "program my_prog;\n"
      "endprogram\n"
      "module m; my_prog u0() endmodule\n"));
}

}  // namespace
