#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "helpers_three_comma_instances.h"

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
  ExpectThreeCommaSeparatedInstances(
      "program my_prog;\n"
      "endprogram\n"
      "module m; my_prog u0(), u1(), u2(); endmodule\n");
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
  auto r = Parse(
      "program my_prog;\n"
      "endprogram\n"
      "module m; my_prog u0() endmodule\n");
  // Parser::ParseModuleInstList files the shared instantiation reports under
  // §23.3.2, whatever kind of design element the leading identifier names.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "23.3.2"));
}

// program_instantiation ::= program_identifier [ parameter_value_assignment ]
//   hierarchical_instance { , hierarchical_instance } ;
// Its sub-symbols are A.4.1.1's: name_of_instance takes A.9.3's
// escaped_identifier, and param_expression is one of A.8.3's
// `mintypmax_expression | data_type | $`.
TEST(ProgramInstantiationGrammar, EscapedNameAndParamExpressionForms) {
  auto r = Parse(
      "program p #(parameter int W = 8, parameter type T = logic) ();\n"
      "endprogram\n"
      "module m;\n"
      "  p #(1:2:3, bit) \\u.0 ();\n"
      "  p #(.W($), .T(int)) u1();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->inst_name, "u.0");
  ASSERT_EQ(items[0]->inst_params.size(), 2u);
  EXPECT_EQ(items[0]->inst_params[0].second->kind, ExprKind::kMinTypMax);
  ASSERT_EQ(items[1]->inst_params.size(), 2u);
  EXPECT_EQ(items[1]->inst_params[0].first, "W");
  EXPECT_EQ(items[1]->inst_params[1].first, "T");
}

// A.1.4's module_common_item admits program_instantiation and A.1.6's
// interface_or_generate_item reaches module_common_item, as §24.3 has it,
// "program blocks can be nested within modules or interfaces"; a program is
// instantiated inside an interface and inside a generate block of it.
TEST(ProgramInstantiationGrammar, ProgramInstantiatedInsideInterface) {
  auto r = Parse(
      "program p(input logic clk); endprogram\n"
      "interface ifc(input logic clk);\n"
      "  p p0(clk);\n"
      "  if (1) begin : g\n"
      "    p p1(.clk(clk));\n"
      "  end\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* inst =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "p");
  EXPECT_EQ(inst->inst_name, "p0");
}

}  // namespace
