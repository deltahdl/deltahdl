// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- net_port_type ---
// [ net_type ] data_type_or_implicit | interconnect implicit_data_type
TEST(ParserA212, NetPortTypeTriType) {
  auto r = ParseWithPreprocessor("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "bus");
}

// --- variable_port_type ---
// var_data_type ::= data_type | var data_type_or_implicit
TEST(ParserA212, VarDataTypeExplicit) {
  // var_data_type: data_type (integer_vector_type)
  auto r = ParseWithPreprocessor(
      "module m(input logic signed [15:0] val); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA212, VarDataTypeInt) {
  // var_data_type: data_type (integer_atom_type)
  auto r = ParseWithPreprocessor("module m(input int count); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

// --- list_of_port_identifiers ---
// port_identifier { unpacked_dimension }
//     { , port_identifier { unpacked_dimension } }
TEST(ParserA23, ListOfPortIdentifiersSingle) {
  auto r = ParseWithPreprocessor("module m(inout wire a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

TEST(ParserA23, ListOfPortIdentifiersWithUnpackedDim) {
  auto r = ParseWithPreprocessor("module m(inout logic a [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
}

// --- list_of_variable_identifiers ---
// variable_identifier { variable_dimension }
//     { , variable_identifier { variable_dimension } }
TEST(ParserA23, ListOfVariableIdentifiersSingle) {
  auto r = ParseWithPreprocessor("module m(input logic d); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA23, ListOfVariableIdentifiersMultipleAnsi) {
  auto r = ParseWithPreprocessor(
      "module m(input logic a, input logic b, input logic c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

TEST(ParserA23, ListOfVariableIdentifiersWithDim) {
  auto r = ParseWithPreprocessor("module m(input logic d [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
}

TEST(ParserA23, ListOfVariablePortIdentifiersMultipleAnsi) {
  auto r = ParseWithPreprocessor(
      "module m(output logic a = 1'b0, output logic b = 1'b1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

TEST(ParserA23, ListOfVariablePortIdentifiersWithDim) {
  auto r = ParseWithPreprocessor(
      "module m(output logic q [1:0] = '{0, 0}); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
  EXPECT_NE(port.default_value, nullptr);
}

TEST(ParserA25, PortWithPackedDim) {
  auto r =
      ParseWithPreprocessor("module m(input logic [15:0] data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  ASSERT_NE(r.cu->modules[0]->ports[0].data_type.packed_dim_left, nullptr);
}

// ansi_port_declaration with default value: input logic a = 1'b0
TEST(SourceText, AnsiPortWithDefault) {
  auto r = ParseWithPreprocessor("module m(input logic a = 1'b0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
}

TEST(ParserA212, OutputDefaultValue) {
  // list_of_variable_port_identifiers: port_id [ = constant_expression ]
  auto r = ParseWithPreprocessor("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(ParserSection23, MacromoduleDefinition) {
  auto r = ParseWithPreprocessor(
      "macromodule top;\n"
      "  wire a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Parser, EmptyModule) {
  auto r = ParseWithPreprocessor("module empty; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(Parser, MultipleModules) {
  auto r = ParseWithPreprocessor(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

// §3.3 Design element instantiations
TEST(ParserClause03, Cl3_3_DesignElementInstantiations) {
  auto r = ParseWithPreprocessor(
      "module child; endmodule\n"
      "module top;\n"
      "  logic sig;\n"
      "  child c0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  // "top" is modules[1]; check it has the instantiation.
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

// Nested module_declaration as non_port_module_item.
TEST(SourceText, NestedModuleDeclaration) {
  auto r = ParseWithPreprocessor(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->nested_module_decl, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->nested_module_decl->name, "inner");
}

// Extern module declaration.
TEST(SourceText, ExternModule) {
  auto r = ParseWithPreprocessor("extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

// 19. Hierarchical reference syntax (a.b.c)
TEST(ParserClause03, Cl3_13_HierarchicalReferenceSyntax) {
  // Hierarchical names like top.sub.sig are member-access expressions.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

// --- Defparam tests ---
TEST(Parser, DefparamSingle) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1);
  EXPECT_NE(item->defparam_assigns[0].first, nullptr);
  EXPECT_NE(item->defparam_assigns[0].second, nullptr);
}

TEST(Parser, DefparamMultiple) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 8, u1.DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 2);
}

// parameter_override: defparam list_of_defparam_assignments.
TEST(SourceText, ParameterOverrideDefparam) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  defparam sub.W = 16, sub.D = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  auto* dp = r.cu->modules[0]->items[0];
  EXPECT_EQ(dp->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(dp->defparam_assigns.size(), 2u);
}

// =============================================================================
// A.2.3 Declaration lists
// =============================================================================
// --- list_of_defparam_assignments ---
// defparam_assignment { , defparam_assignment }
TEST(ParserA23, ListOfDefparamAssignmentsSingle) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 1u);
}

TEST(ParserA23, ListOfDefparamAssignmentsMultiple) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 16, u1.DEPTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 2u);
}

// =============================================================================
// A.2.4 Declaration assignments
// =============================================================================
// --- defparam_assignment ---
// hierarchical_parameter_identifier = constant_mintypmax_expression
TEST(ParserA24, DefparamAssignmentHierarchical) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.sub.WIDTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1u);
  // The path expression should be a hierarchical reference
  EXPECT_NE(item->defparam_assigns[0].first, nullptr);
  EXPECT_NE(item->defparam_assigns[0].second, nullptr);
}

TEST(ParserA24, DefparamAssignmentMintypmax) {
  // constant_mintypmax_expression: expr : expr : expr
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.DELAY = 1:2:3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1u);
}

// =============================================================================
// A.1.2 bind_directive (§23.11)
// =============================================================================
// Form 1: bind target_scope bind_instantiation
TEST(SourceText, BindDirectiveBasic) {
  auto r =
      ParseWithPreprocessor("bind target_mod checker_mod chk_inst(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target_mod");
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
  ASSERT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_module,
            "checker_mod");
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_name, "chk_inst");
}

// Form 1 with instance list: bind scope : inst1, inst2 instantiation
TEST(SourceText, BindDirectiveWithInstanceList) {
  auto r = ParseWithPreprocessor("bind dut : i1, i2 chk chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "dut");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0], "i1");
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[1], "i2");
}

// Form 2: bind hierarchical_instance instantiation
TEST(SourceText, BindDirectiveHierarchical) {
  auto r = ParseWithPreprocessor("bind top.dut.u1 checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.dut.u1");
}

}  // namespace
