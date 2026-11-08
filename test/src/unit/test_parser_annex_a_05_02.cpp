#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
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

TEST(UdpPortGrammar, EscapedPortIdentifiers) {
  auto r = Parse(
      "primitive p1 (\\q+ , \\a.0 , b);\n"
      "  output \\q+ ;\n"
      "  reg \\q+ ;\n"
      "  input \\a.0 , b;\n"
      "  table\n"
      "    0 0 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive p2 (output \\o- , input \\i- );\n"
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

TEST(UdpPortGrammar, AttributeBeforeAPortListOfNamesIsRejected) {
  auto r = Parse(
      "primitive p((* keep *) y, a);\n"
      "  output y;\n"
      "  input a;\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "extern primitive q((* keep *) y, a);\n");
  const char* const kMsg =
      "a UDP's port list of names takes no attribute instance";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 1, "A.5.2"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 6, "A.5.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[1]->output_name, "y");
  EXPECT_EQ(r.cu->udps[1]->input_names.size(), 1u);
}

TEST(UdpPortGrammar, AttributeBeforeADeclarationListIsKept) {
  auto r = Parse(
      "primitive p((* keep *) output y, input a);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "extern primitive q((* keep *) output y, input a);\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
