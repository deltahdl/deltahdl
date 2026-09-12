#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpPortGrammar, OutputDeclAnsi_RegInitZero) {
  auto r = Parse(
      "primitive dff(output reg q = 1'b0, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

TEST(UdpPortGrammar, OutputDeclNonAnsi_RegInitZero) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output reg q = 1'b0;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

TEST(UdpPortGrammar, OutputDeclWildcard_RegInit) {
  auto r = Parse(
      "primitive dff(.*);\n"
      "  output reg q = 1'b0;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

TEST(UdpPortGrammar, SimPortLevelInit) {
  auto r = Parse(
      "primitive latch(output reg q = 1'b0, input d, input en);\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '0'});
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpPortGrammar, SimNonAnsiPortLevelInit) {
  auto r = Parse(
      "primitive latch(q, d, en);\n"
      "  output reg q = 1'b1;\n"
      "  input d, en;\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '1'});
  EXPECT_EQ(state.GetOutput(), '0');
}

// udp_declaration_port_list: the optional { attribute_instance } prefix on
// udp_output_declaration and udp_input_declaration is consumed by the ANSI
// header parser; the surrounding port grammar must still parse normally.
TEST(UdpPortGrammar, AttributesOnAnsiPortDeclarations) {
  auto r = Parse(
      "primitive dff((* keep *) output reg q = 1'b0,"
      " (* foo = 1 *) input d, (* bar *) input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "d");
  EXPECT_EQ(udp->input_names[1], "clk");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

// udp_port_declaration: each of udp_output_declaration, udp_reg_declaration and
// udp_input_declaration carries an optional { attribute_instance } prefix in
// the non-ANSI body. The prefixes must be consumed without disturbing the port
// set.
TEST(UdpPortGrammar, AttributesOnNonAnsiPortDeclarations) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  (* keep *) output q;\n"
      "  (* synth *) reg q;\n"
      "  (* foo = 2 *) input d, clk;\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "d");
  EXPECT_EQ(udp->input_names[1], "clk");
  EXPECT_TRUE(udp->is_sequential);
}

// udp_declaration_port_list with the first alternative of
// udp_output_declaration
// ({ attribute_instance } output port_identifier) — a combinational UDP whose
// ANSI output port carries no reg keyword, so the primitive is not sequential.
TEST(UdpPortGrammar, CombinationalOutputDeclAnsi) {
  auto r = Parse(
      "primitive and_udp(output q, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_FALSE(udp->is_sequential);
  EXPECT_FALSE(udp->has_initial);
}

// udp_output_declaration second alternative with the optional [ =
// constant_expression ] omitted: a sequential reg output that declares no
// port-level initial value.
TEST(UdpPortGrammar, OutputRegDeclWithoutInitializer) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "q");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_FALSE(udp->has_initial);
}

// udp_port_declaration requires each declaration to be terminated by a
// semicolon; dropping it on a non-ANSI body declaration is rejected.
TEST(UdpPortGrammar, NonAnsiPortDeclarationMissingSemicolon) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output reg q = 1'b0;\n"
      "  input d, clk\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.2 owns the UDP port declarations, so Parser::ParseUdpPortDecls files
  // the missing semicolon there rather than under A.5.2.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'table'", 4, "29.3.2"));
}

TEST(UdpPortGrammar, SimStandaloneRegSequential) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  reg q;\n"
      "  input d, clk;\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "    ? f : ? : -;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), '0');

  state.SetInputs({'1', '0'});
  state.EvaluateWithEdge({'1', '1'}, 1, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

// udp_output_declaration's second alternative writes `output reg
// port_identifier [ = constant_expression ]`: the value is an expression, not
// one of A.5.3's init_val literals, so `~1'b0` is a negation of the literal
// rather than the literal that ends its spelling. The parser keeps the
// expression as written for the run to evaluate.
TEST(UdpPortGrammar, AnsiOutputRegInitialValueIsKeptAsAnExpression) {
  auto r = Parse(
      "primitive dff(output reg q = ~1'b0, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  ASSERT_NE(udp->initial_expr, nullptr);
  EXPECT_EQ(udp->initial_expr->kind, ExprKind::kUnary);
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[1], "clk");
}

TEST(UdpPortGrammar, NonAnsiOutputRegInitialValueIsKeptAsAnExpression) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output reg q = 1'b1 & 1'b1;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  ASSERT_NE(udp->initial_expr, nullptr);
  EXPECT_EQ(udp->initial_expr->kind, ExprKind::kBinary);
  ASSERT_EQ(udp->input_names.size(), 2u);
}

// A literal initial value is read as the one bit a 1-bit reg keeps of it, its
// least significant bit, rather than as the last character of its spelling: `3`
// ends in a character that is neither 0 nor 1, and `4'h3` likewise, yet both
// stand for a value whose low bit is 1.
TEST(UdpPortGrammar, LiteralInitialValueIsItsLeastSignificantBit) {
  auto r = Parse(
      "primitive p_dec(output reg q = 3, input d);\n"
      "  table\n"
      "    0 : ? : 0;\n"
      "    1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive p_hex(output reg q = 4'h3, input d);\n"
      "  table\n"
      "    0 : ? : 0;\n"
      "    1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive p_unknown(output reg q = 2'b1x, input d);\n"
      "  table\n"
      "    0 : ? : 0;\n"
      "    1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive p_bin(output reg q = 2'b10, input d);\n"
      "  table\n"
      "    0 : ? : 0;\n"
      "    1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 4u);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
  EXPECT_EQ(r.cu->udps[1]->initial_value, '1');
  EXPECT_EQ(r.cu->udps[2]->initial_value, 'x');
  EXPECT_EQ(r.cu->udps[3]->initial_value, '0');
}

// udp_output_declaration's first alternative is `output port_identifier` with
// no initial value: the `[ = constant_expression ]` belongs to the `output reg`
// alternative alone. An initial value on an output declared without reg is
// reported at its `=`, and the declaration is otherwise taken as written so
// the header's port count still agrees with the table below.
TEST(UdpPortGrammar, AnsiOutputWithoutRegTakesNoInitialValue) {
  auto r = Parse(
      "primitive p(output q = 1'b0, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output port takes an initial value only as 'output reg'", 1,
      "A.5.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "q");
  EXPECT_EQ(r.cu->udps[0]->input_names.size(), 2u);
  EXPECT_FALSE(r.cu->udps[0]->has_initial);
}

TEST(UdpPortGrammar, NonAnsiOutputWithoutRegTakesNoInitialValue) {
  auto r = Parse(
      "primitive p(q, a, b);\n"
      "  output q = 1'b0;\n"
      "  input a, b;\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output port takes an initial value only as 'output reg'", 2,
      "A.5.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names.size(), 2u);
  EXPECT_FALSE(r.cu->udps[0]->has_initial);
}

// Every identifier A.5.2 writes -- port_identifier in udp_port_list and the
// two port declarations, variable_identifier in udp_reg_declaration -- is
// A.9.3's `simple_identifier | escaped_identifier`. The parser looked for a
// simple identifier at each, so a UDP whose ports carried escaped names was
// reported as a missing identifier in either header form.
TEST(UdpPortGrammar, EscapedPortIdentifiers) {
  auto r = Parse(
      "primitive p1 (\\q+, \\a.0, b);\n"
      "  output \\q+;\n"
      "  reg \\q+;\n"
      "  input \\a.0, b;\n"
      "  table\n"
      "    0 0 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive p2 (output \\o-, input \\i-);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "q+");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "a.0");
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  EXPECT_EQ(r.cu->udps[1]->output_name, "o-");
  ASSERT_EQ(r.cu->udps[1]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[1]->input_names[0], "i-");
}

// udp_reg_declaration ::= { attribute_instance } reg variable_identifier, and
// udp_input_declaration ::= { attribute_instance } input
// list_of_udp_port_identifiers: neither carries `= constant_expression`, which
// A.5.2 writes on `output reg` alone. An initial value on either was reported
// as a missing ';' or ')'.
TEST(UdpPortGrammar, InitialValueOnRegOrInputDeclarationIsRejected) {
  auto r = Parse(
      "primitive p1 (q, a);\n"
      "  output q;\n"
      "  reg q = 1'b0;\n"
      "  input a = 1'b1;\n"
      "  table 0 : ? : 0; 1 : ? : 1; endtable\n"
      "endprimitive\n"
      "primitive p2 (output o, input i = 1'b0);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a UDP reg declaration takes no initial value", 3, "A.5.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a UDP input declaration takes no initial value", 4, "A.5.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a UDP input declaration takes no initial value", 7, "A.5.2"));
  EXPECT_FALSE(ReportedError(r.diags, "expected ';'", 3, "29.3.2"));
  EXPECT_FALSE(ReportedError(r.diags, "expected ';'", 4, "29.3.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[1]->input_names.size(), 1u);
}

}  // namespace
