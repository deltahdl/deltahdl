#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpDeclGrammar, PrimitiveKeywordIntroducesUdp) {
  auto r = Parse(
      "primitive udp_buf (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_buf");
}

TEST(UdpDeclGrammar, AnsiCombinational) {
  auto r = Parse(
      "primitive and_gate(output out, input a, input b);\n"
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
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  ASSERT_EQ(udp->table.size(), 4u);
}

TEST(UdpDeclGrammar, NonAnsiWithPortDecls) {
  auto r = Parse(
      "primitive inv(out, in);\n"
      "  output out;\n"
      "  input in;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "inv");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "in");
}

TEST(UdpDeclGrammar, MissingEndprimitiveIsError) {
  EXPECT_FALSE(
      ParseOk("primitive inv(output y, input a);\n"
              "  table\n"
              "    0 : 1;\n"
              "    1 : 0;\n"
              "  endtable\n"));
}

TEST(UdpDeclGrammar, UdpWithNoOutputPortRejected) {
  auto r = Parse(
      "primitive p(a, b);\n"
      "  input a;\n"
      "  input b;\n"
      "  table 0 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpWithNoInputPortsRejected) {
  auto r = Parse(
      "primitive p(q);\n"
      "  output q;\n"
      "  table : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpWithDuplicateOutputsRejected) {
  auto r = Parse(
      "primitive p(a, b, c);\n"
      "  output a;\n"
      "  output b;\n"
      "  input c;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpDuplicateOutputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output a, output b, input c);\n"
      "  table 0 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpInoutPortInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output o, inout io);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpInoutPortInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(o, io);\n"
      "  output o;\n"
      "  inout io;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpVectorOutputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output [3:0] q, input a);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpVectorInputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output q, input [3:0] a);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpVectorOutputInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(q, a);\n"
      "  output [3:0] q;\n"
      "  input a;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpVectorInputInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(o, a);\n"
      "  output o;\n"
      "  input [3:0] a;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpOutputNotFirstInNonAnsiPortListRejected) {
  auto r = Parse(
      "primitive p(a, q);\n"
      "  input a;\n"
      "  output q;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpDeclGrammar, UdpHeaderWithoutStateTableRejected) {
  auto r = Parse(
      "primitive p(output o, input a);\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
