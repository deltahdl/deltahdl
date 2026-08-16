#include "fixture_parser.h"
#include "helpers_reported_error.h"
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

// §29.3: a UDP definition is terminated by the endprimitive keyword, so a
// definition that ends after endtable is incomplete. The annex A.5.1 file
// carries the same requirement stated as the udp_declaration production.
TEST(UdpDeclGrammar, UdpDefinitionWithoutEndprimitiveIsError) {
  auto r = Parse(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n");
  // Parser::ParseUdpDecl demands endprimitive under §29.3; the source runs out
  // first, so the report stands on line 6, past the last written line.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endprimitive', got EOF", 6, "29.3"));
}

TEST(UdpDeclGrammar, UdpWithNoOutputPortRejected) {
  auto r = Parse(
      "primitive p(a, b);\n"
      "  input a;\n"
      "  input b;\n"
      "  table 0 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "UDP shall have exactly one output port",
                            1, "29.3.1"));
}

TEST(UdpDeclGrammar, UdpWithNoInputPortsRejected) {
  auto r = Parse(
      "primitive p(q);\n"
      "  output q;\n"
      "  table : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "UDP shall have at least one input port",
                            1, "29.3.1"));
}

TEST(UdpDeclGrammar, UdpAnsiHeaderWithNoInputPortRejected) {
  // §29.3.1: a UDP must have at least one input port. This exercises the
  // requirement in the ANSI (port-declaration) header form, where the output
  // is declared inline and no input port follows it.
  auto r = Parse(
      "primitive p(output q);\n"
      "  table : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "UDP shall have at least one input port",
                            1, "29.3.1"));
}

TEST(UdpDeclGrammar, UdpWithDuplicateOutputsRejected) {
  auto r = Parse(
      "primitive p(a, b, c);\n"
      "  output a;\n"
      "  output b;\n"
      "  input c;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  // Parser::ParseUdpOutputDecl reports the second output declaration where it
  // stands, on line 3.
  EXPECT_TRUE(ReportedError(r.diags, "UDP shall have exactly one output port",
                            3, "29.3.1"));
}

// §29.3.1: "UDPs have multiple input ports and exactly one output port". The
// header is A.5.2's `udp_declaration_port_list`, whose entries are port
// declarations, so a second `output` is a second output declaration rather than
// a port name gone missing. The header is written over three lines because the
// report's line is what says which `output` was named: on one line a report
// about the first satisfies the assertion too.
TEST(UdpDeclGrammar, UdpDuplicateOutputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output a,\n"
      "            output b,\n"
      "            input c);\n"
      "  table 0 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "UDP shall have exactly one output port",
                            2, "29.3.1"));
}

TEST(UdpDeclGrammar, UdpInoutPortInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output o, inout io);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP ports shall be input or output; inout not permitted", 1,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpInoutPortInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(o, io);\n"
      "  output o;\n"
      "  inout io;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP ports shall be input or output; inout not permitted", 3,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpInoutAsLeadingPortRejected) {
  // §29.3.1: inout is barred regardless of position in the port list. Here the
  // inout appears as the very first port, before the header disambiguates into
  // its ANSI or non-ANSI form, so a distinct production path guards the rule.
  auto r = Parse(
      "primitive p(inout io, output o, input a);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP ports shall be input or output; inout not permitted", 1,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpVectorOutputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output [3:0] q, input a);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP port shall be scalar; vector range not permitted", 1,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpVectorInputInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(output q, input [3:0] a);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP port shall be scalar; vector range not permitted", 1,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpVectorOutputInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(q, a);\n"
      "  output [3:0] q;\n"
      "  input a;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP port shall be scalar; vector range not permitted", 2,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpVectorInputInNonAnsiDeclRejected) {
  auto r = Parse(
      "primitive p(o, a);\n"
      "  output o;\n"
      "  input [3:0] a;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP port shall be scalar; vector range not permitted", 3,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpOutputNotFirstInNonAnsiPortListRejected) {
  auto r = Parse(
      "primitive p(a, q);\n"
      "  input a;\n"
      "  output q;\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  // The report stands on the offending port-list entry, which is on line 1.
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output port shall be the first port in the port list", 1,
      "29.3.1"));
}

// §29.3.1: "The output port shall be the first port in the port list." A header
// beginning `input` holds port declarations, so it is A.5.2's
// `udp_declaration_port_list` with its entries in the wrong order rather than a
// `udp_port_list` whose first name is missing. The report stands at the
// misplaced port, on a line of its own so that the assertion cannot be
// satisfied by a report about the output declaration below it.
TEST(UdpDeclGrammar, UdpOutputNotFirstInAnsiHeaderRejected) {
  auto r = Parse(
      "primitive p(input a,\n"
      "            output o);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output port shall be the first port in the port list", 1,
      "29.3.1"));
}

// The same header read for what it leaves behind. Reading it as A.5.2's
// `udp_port_list` put the `input` keyword's own spelling where the output port
// belongs and the `output` keyword's among the inputs, so the ports the user
// declared are what says the header was read as the declarations it is.
TEST(UdpDeclGrammar,
     UdpAnsiHeaderWithOutputSecondStillReadsItsPortsAsDeclarations) {
  auto r = Parse(
      "primitive p(input a,\n"
      "            output o);\n"
      "  table 0 : 0; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "o");
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "a");
}

// §29.3.1's one-output rule holds over `extern udp_ansi_declaration` as much as
// over the full declaration. A.5.1 gives that form no `udp_body`, so the header
// is the only place the rule can be reported.
TEST(UdpDeclGrammar, ExternUdpDuplicateOutputRejected) {
  auto r = Parse(
      "extern primitive p(output a,\n"
      "                   output b);\n");
  EXPECT_TRUE(ReportedError(r.diags, "UDP shall have exactly one output port",
                            2, "29.3.1"));
}

// The output-first rule for the same prototype form. With no `udp_body` there
// are no separate port declarations for ReconcileUdpNonAnsiPortList to compare
// the list against, so nothing else in the source can name this rule.
TEST(UdpDeclGrammar, ExternUdpOutputNotFirstRejected) {
  auto r = Parse(
      "extern primitive p(input a,\n"
      "                   output o);\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output port shall be the first port in the port list", 1,
      "29.3.1"));
}

TEST(UdpDeclGrammar, UdpHeaderWithoutStateTableRejected) {
  auto r = Parse(
      "primitive p(output o, input a);\n"
      "endprimitive\n");
  // §29.3.4 owns the udp_body table, so Parser::ParseUdpTable files the
  // missing `table` keyword there rather than under §29.3.1.
  EXPECT_TRUE(ReportedError(r.diags, "expected 'table', got 'endprimitive'", 2,
                            "29.3.4"));
}

}  // namespace
