#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// A UDP without a reg declaration is combinational; the parser must not
// flag it as sequential.
TEST(UdpPortDeclaration, UdpCombinational) {
  auto r = Parse(
      "primitive mux2(output y, input a, input b, input s);\n"
      "  table\n"
      "    0 ? 0 : 0 ;\n"
      "    1 ? 0 : 1 ;\n"
      "    ? 0 1 : 0 ;\n"
      "    ? 1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "mux2");
  EXPECT_FALSE(r.cu->udps[0]->is_sequential);
}

// A UDP with only one input port is legal; the input declaration satisfies
// the "one or more input port names" rule with a single identifier.
TEST(UdpPortDeclaration, SingleInput) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
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
  EXPECT_EQ(udp->input_names[0], "in");
  ASSERT_EQ(udp->table.size(), 2u);
  ASSERT_EQ(udp->table[0].inputs.size(), 1u);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].output, '1');
}

// `output reg` in an ANSI header marks the UDP as sequential without needing
// a separate reg declaration.
TEST(UdpPortDeclaration, AnsiSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
  ASSERT_EQ(udp->table.size(), 2u);
}

// In the non-ANSI form, `output reg q` in the body also makes the UDP
// sequential; the reg token is the signal that triggers sequential mode.
TEST(UdpPortDeclaration, NonAnsiSequentialWithReg) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output reg q;\n"
      "  input d;\n"
      "  input clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "d");
  EXPECT_EQ(udp->input_names[1], "clk");
}

// A single `input` keyword shared across several comma-separated identifiers
// introduces multiple input ports at once.
TEST(UdpPortDeclaration, AnsiSharedInputKeyword) {
  auto r = Parse(
      "primitive mux(output out, input a, b, sel);\n"
      "  table\n"
      "    0 ? 0 : 0;\n"
      "    1 ? 0 : 1;\n"
      "    ? 0 1 : 0;\n"
      "    ? 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "sel");
}

// A UDP may carry many input ports; the parser must not cap the count.
TEST(UdpPortDeclaration, ManyInputs) {
  auto r = Parse(
      "primitive gate5(output out, input a, b, c, d, e);\n"
      "  table\n"
      "    0 0 0 0 0 : 0;\n"
      "    1 1 1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 5u);
  EXPECT_EQ(udp->input_names[4], "e");
  ASSERT_EQ(udp->table[0].inputs.size(), 5u);
}

// A single `input` keyword may be followed by any number of comma-separated
// identifiers, including a mix from different parenthesized positions.
TEST(UdpPortDeclaration, AnsiPortListMixedInputKeyword) {
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

// Non-ANSI body `output out;` with no reg declaration leaves the UDP
// combinational.
TEST(UdpPortDeclaration, OutputDeclPlain) {
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

// A non-ANSI UDP may mix plain `output`, `input`, and standalone `reg`
// declarations; the three alternatives coexist in one body.
TEST(UdpPortDeclaration, AllThreeDeclarationAlternatives) {
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

// A non-ANSI input declaration with a single identifier is legal.
TEST(UdpPortDeclaration, InputDeclSingleId) {
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

// A non-ANSI input declaration may list several identifiers separated by
// commas under a single `input` keyword.
TEST(UdpPortDeclaration, InputDeclMultipleIds) {
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

// Attributes are permitted on an output port declaration.
TEST(UdpPortDeclaration, AttrOnOutputDecl) {
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

// Attributes are permitted on a reg port declaration.
TEST(UdpPortDeclaration, AttrOnRegDecl) {
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

// Input identifiers can be split across a comma list in one declaration and
// additional separate `input` declarations.
TEST(UdpPortDeclaration, InputDeclMixedListAndSeparate) {
  auto r = Parse(
      "primitive gate(out, a, b, c, d);\n"
      "  output out;\n"
      "  input a, b;\n"
      "  input c;\n"
      "  input d;\n"
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

// A non-ANSI UDP with two inputs: the port list gives bare names and the
// separate declarations specify output and inputs.
TEST(UdpPortDeclaration, NonAnsiPortListTwoInputs) {
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

// A non-ANSI UDP with five inputs demonstrates that the port-decl parser
// handles long comma-separated input lists.
TEST(UdpPortDeclaration, NonAnsiPortListFiveInputs) {
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

// Each separate `input` declaration appends identifiers to the input list
// in the order they appear.
TEST(UdpPortDeclaration, InputDeclSeparateDecls) {
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

// Reg declarations are legal immediately after the output declaration.
TEST(UdpPortDeclaration, RegDeclAfterOutput) {
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

// Attributes are permitted on an input port declaration.
TEST(UdpPortDeclaration, AttrOnInputDecl) {
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

// A sequential UDP with 9 inputs must be accepted: the LRM requires
// implementations to allow at least 9 inputs for sequential UDPs.
TEST(UdpPortDeclaration, NineInputsSequential) {
  auto r = Parse(
      "primitive big_seq(output reg q, input i0, i1, i2, i3, i4, i5, i6, i7,"
      " clk);\n"
      "  table\n"
      "    0 0 0 0 0 0 0 0 r : ? : 0;\n"
      "    1 1 1 1 1 1 1 1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->input_names.size(), 9u);
}

// A combinational UDP with 10 inputs must be accepted: the LRM requires
// implementations to allow at least 10 inputs for combinational UDPs.
TEST(UdpPortDeclaration, TenInputsCombinational) {
  auto r = Parse(
      "primitive big_comb(output y, input a, b, c, d, e, f, g, h, i, j);\n"
      "  table\n"
      "    0 0 0 0 0 0 0 0 0 0 : 0;\n"
      "    1 1 1 1 1 1 1 1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->input_names.size(), 10u);
}

// The output port declaration is defined to be the keyword `output` followed
// by one output port name; a comma-separated list of names is rejected.
TEST(UdpPortDeclaration, OutputDeclMultipleNamesRejected) {
  auto r = Parse(
      "primitive bad(a, b, c);\n"
      "  output a, b;\n"
      "  input c;\n"
      "  table\n"
      "    0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A separate reg declaration in the body must name the output port; naming a
// non-output identifier is rejected.
TEST(UdpPortDeclaration, RegDeclNotNamingOutputRejected) {
  auto r = Parse(
      "primitive bad(q, d, clk);\n"
      "  output q;\n"
      "  reg d;\n"
      "  input d;\n"
      "  input clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
