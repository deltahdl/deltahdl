// §23.3.2: Module instantiation syntax

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.4.1.1 -- Module instantiation
//
// module_instantiation ::=
//   module_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- module_instantiation: basic ---
TEST(ParserAnnexA0411, BasicModuleInst) {
  auto r = Parse("module m; sub u0(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- module_instantiation: multiple hierarchical_instance ---
// module_identifier [#(...)] inst1(...), inst2(...), inst3(...) ;
TEST(ParserAnnexA0411, MultipleHierarchicalInstances) {
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

TEST(ParserAnnexA0411, MultipleInstancesWithParams) {
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

// =============================================================================
// parameter_value_assignment ::= # ( [ list_of_parameter_value_assignments ] )
// list_of_parameter_value_assignments ::=
//   ordered_parameter_assignment { , ordered_parameter_assignment }
//   | named_parameter_assignment { , named_parameter_assignment }
// ordered_parameter_assignment ::= param_expression
// named_parameter_assignment ::= . parameter_identifier ( [ param_expression ]
// )
// =============================================================================
TEST(ParserAnnexA0411, EmptyParameterValueAssignment) {
  // #() — empty parameter list
  auto r = Parse("module m; sub #() u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 0u);
}

TEST(ParserAnnexA0411, FullCombination) {
  // Named params, instance array, named ports, wildcard
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

TEST(ParserAnnexA0411, MultipleInstancesSharedParams) {
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

// --- interface_instantiation: with empty parameter ---
TEST(ParserAnnexA0412, InterfaceInstEmptyParam) {
  auto r = Parse("module m; my_if #() u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_TRUE(item->inst_params.empty());
}

// --- program_instantiation: empty parameter list ---
TEST(ParserAnnexA0413, ProgramInstEmptyParam) {
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

}  // namespace
