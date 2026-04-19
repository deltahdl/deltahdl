#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// The primitive keyword introduces a UDP definition and the following
// identifier names it.
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

// The ANSI header form carries port declarations directly in the parenthesized
// list; the parser must capture the output and each input from that list.
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

// The non-ANSI header form lists bare port names in parentheses and carries
// the port direction information in separate declarations between the header
// and the state table.
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

// A UDP definition without a trailing endprimitive is not a valid definition.
TEST(UdpDeclGrammar, MissingEndprimitiveIsError) {
  EXPECT_FALSE(ParseOk(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"));
}

// A declaration that never names an output port is not a well-formed UDP.
TEST(UdpDeclGrammar, UdpWithNoOutputPortRejected) {
  auto r = Parse(
      "primitive p(a, b);\n"
      "  input a;\n"
      "  input b;\n"
      "  table 0 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A UDP with only an output and no inputs cannot model any combinational or
// sequential behavior and shall be rejected.
TEST(UdpDeclGrammar, UdpWithNoInputPortsRejected) {
  auto r = Parse(
      "primitive p(q);\n"
      "  output q;\n"
      "  table : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Declaring the output twice in a non-ANSI body is a second output, which
// violates the one-output-per-UDP rule.
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

// An inout keyword in the ANSI header port list is not a legal UDP port
// direction.
TEST(UdpDeclGrammar, UdpInoutPortInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output o, inout io);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// An inout port declaration following a non-ANSI UDP header is not a legal
// UDP port direction.
TEST(UdpDeclGrammar, UdpInoutPortInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(o, io);\n"
      "  output o;\n"
      "  inout io;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A packed range on the output port in an ANSI header makes the port
// non-scalar.
TEST(UdpDeclGrammar, UdpVectorOutputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output [3:0] q, input a);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A packed range on an input port in an ANSI header makes the port non-scalar.
TEST(UdpDeclGrammar, UdpVectorInputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output q, input [3:0] a);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A packed range on a non-ANSI output port declaration also makes the port
// non-scalar.
TEST(UdpDeclGrammar, UdpVectorOutputInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(q, a);\n"
      "  output [3:0] q;\n"
      "  input a;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The output port must lead the non-ANSI port list; placing an input first
// makes the listed order incompatible with the direction given by the
// declarations.
TEST(UdpDeclGrammar, UdpOutputNotFirstInNonAnsiPortListRejected) {
  auto r = Parse(
      "primitive p(a, q);\n"
      "  input a;\n"
      "  output q;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
