#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/udp_eval.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

}  // namespace

// =============================================================================
// A.5.2 -- UDP ports
//
// udp_port_list ::=
//   output_port_identifier , input_port_identifier
//     { , input_port_identifier }
//
// udp_declaration_port_list ::=
//   udp_output_declaration , udp_input_declaration
//     { , udp_input_declaration }
//
// udp_port_declaration ::=
//   udp_output_declaration ;
//   | udp_input_declaration ;
//   | udp_reg_declaration ;
//
// udp_output_declaration ::=
//   { attribute_instance } output port_identifier
//   | { attribute_instance } output reg port_identifier
//       [ = constant_expression ]
//
// udp_input_declaration ::=
//   { attribute_instance } input list_of_udp_port_identifiers
//
// udp_reg_declaration ::=
//   { attribute_instance } reg variable_identifier
// =============================================================================

// ---------------------------------------------------------------------------
// udp_port_list (non-ANSI identifier list)
// ---------------------------------------------------------------------------

// Non-ANSI port list with two inputs
TEST(ParserAnnexA052, NonAnsiPortList_TwoInputs) {
  auto r = Parse(
      "primitive and_gate(out, a, b);\n"
      "  output out;\n"
      "  input a, b;\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "and_gate");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4u);
}

// Non-ANSI port list with five inputs
TEST(ParserAnnexA052, NonAnsiPortList_FiveInputs) {
  auto r = Parse(
      "primitive gate5(out, a, b, c, d, e);\n"
      "  output out;\n"
      "  input a, b, c, d, e;\n"
      "  table\n"
      "    0 0 0 0 0 : 0;\n"
      "    1 1 1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 5u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
  EXPECT_EQ(udp->input_names[3], "d");
  EXPECT_EQ(udp->input_names[4], "e");
}

// ---------------------------------------------------------------------------
// udp_declaration_port_list (ANSI port declarations)
// ---------------------------------------------------------------------------

// ANSI port list with single input
TEST(ParserAnnexA052, AnsiPortList_SingleInput) {
  auto r = Parse(
      "primitive inv(output out, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "a");
}

// ANSI port list with mixed input keyword usage
// (some inputs have 'input' keyword, some share the previous one)
TEST(ParserAnnexA052, AnsiPortList_MixedInputKeyword) {
  auto r = Parse(
      "primitive gate(output out, input a, input b, c);\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
}

// ---------------------------------------------------------------------------
// udp_port_declaration — all three alternatives
// ---------------------------------------------------------------------------

// udp_output_declaration ; (plain output)
TEST(ParserAnnexA052, PortDecl_OutputPlain) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  output out;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "out");
  EXPECT_FALSE(udp->is_sequential);
}

// udp_output_declaration ; (output reg)
TEST(ParserAnnexA052, PortDecl_OutputReg) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output reg q;\n"
      "  input d, clk;\n"
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
}

// udp_input_declaration ; (comma-separated list)
TEST(ParserAnnexA052, PortDecl_InputList) {
  auto r = Parse(
      "primitive gate(out, a, b, c);\n"
      "  output out;\n"
      "  input a, b, c;\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
}

// udp_reg_declaration ; (standalone reg after output)
TEST(ParserAnnexA052, PortDecl_RegStandalone) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  reg q;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "q");
  // The separate 'reg q;' declaration should make this sequential
  EXPECT_TRUE(udp->is_sequential);
}

// All three udp_port_declaration alternatives together
TEST(ParserAnnexA052, PortDecl_AllThreeAlternatives) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d;\n"
      "  input clk;\n"
      "  reg q;\n"
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

// ---------------------------------------------------------------------------
// udp_output_declaration — output reg with = constant_expression
// ---------------------------------------------------------------------------

// ANSI form: output reg q = 1'b0
TEST(ParserAnnexA052, OutputDeclAnsi_RegInitZero) {
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

// ANSI form: output reg q = 1'b1
TEST(ParserAnnexA052, OutputDeclAnsi_RegInitOne) {
  auto r = Parse(
      "primitive dff(output reg q = 1'b1, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

// ANSI form: output reg q = 1'bx
TEST(ParserAnnexA052, OutputDeclAnsi_RegInitX) {
  auto r = Parse(
      "primitive dff(output reg q = 1'bx, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, 'x');
}

// Non-ANSI form: output reg q = 1'b0 ; (in port declaration)
TEST(ParserAnnexA052, OutputDeclNonAnsi_RegInitZero) {
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

// Non-ANSI form: output reg q = 1'b1 ; (in port declaration)
TEST(ParserAnnexA052, OutputDeclNonAnsi_RegInitOne) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output reg q = 1'b1;\n"
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
  EXPECT_EQ(udp->initial_value, '1');
}

// Wildcard form: output reg q = 1'b0 ; (in port declaration after .*)
TEST(ParserAnnexA052, OutputDeclWildcard_RegInit) {
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

// ---------------------------------------------------------------------------
// udp_input_declaration — list_of_udp_port_identifiers
// ---------------------------------------------------------------------------

// Single input identifier
TEST(ParserAnnexA052, InputDecl_SingleId) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  output out;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "a");
}

// Multiple input identifiers in single declaration
TEST(ParserAnnexA052, InputDecl_MultipleIds) {
  auto r = Parse(
      "primitive gate(out, a, b, c, d);\n"
      "  output out;\n"
      "  input a, b, c, d;\n"
      "  table\n"
      "    0 0 0 0 : 0;\n"
      "    1 1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 4u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
  EXPECT_EQ(udp->input_names[3], "d");
}

// Multiple separate input declarations
TEST(ParserAnnexA052, InputDecl_SeparateDecls) {
  auto r = Parse(
      "primitive gate(out, a, b, c);\n"
      "  output out;\n"
      "  input a;\n"
      "  input b;\n"
      "  input c;\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
}

// ---------------------------------------------------------------------------
// udp_reg_declaration (standalone reg)
// ---------------------------------------------------------------------------

// Standalone reg declaration after output (no 'reg' on output line)
TEST(ParserAnnexA052, RegDecl_AfterOutput) {
  auto r = Parse(
      "primitive latch(q, d, en);\n"
      "  output q;\n"
      "  reg q;\n"
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
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
}

// Standalone reg declaration after inputs
TEST(ParserAnnexA052, RegDecl_AfterInputs) {
  auto r = Parse(
      "primitive latch(q, d, en);\n"
      "  output q;\n"
      "  input d, en;\n"
      "  reg q;\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
}

// ---------------------------------------------------------------------------
// { attribute_instance } on port declarations
// ---------------------------------------------------------------------------

// Attribute on output declaration
TEST(ParserAnnexA052, AttrOnOutputDecl) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  (* synthesis = \"off\" *) output out;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "out");
}

// Attribute on input declaration
TEST(ParserAnnexA052, AttrOnInputDecl) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  output out;\n"
      "  (* synthesis = \"off\" *) input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "a");
}

// Attribute on reg declaration
TEST(ParserAnnexA052, AttrOnRegDecl) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d, clk;\n"
      "  (* synthesis = \"off\" *) reg q;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
}

// ---------------------------------------------------------------------------
// Simulation — port-level initial value semantics
// ---------------------------------------------------------------------------

// Port-level initialization via output reg q = 1'b0 should work like initial
TEST(ParserAnnexA052, SimPortLevelInit) {
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

// Non-ANSI port-level initialization should also work for simulation
TEST(ParserAnnexA052, SimNonAnsiPortLevelInit) {
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

// Standalone reg declaration should make UDP sequential for simulation
TEST(ParserAnnexA052, SimStandaloneRegSequential) {
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
