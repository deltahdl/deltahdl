#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

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

TEST(UdpPortDeclaration, SequentialUdpWithoutRegRejected) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
