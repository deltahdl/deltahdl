// §29.3.1: UDP header

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_declaration: wildcard port form primitive id ( .* ) ---
TEST(ParserAnnexA051, WildcardPort) {
  auto r = Parse(
      "primitive inv(.*);\n"
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
  ASSERT_EQ(udp->table.size(), 2u);
}

// --- udp_nonansi_declaration: non-ANSI with separate port declarations ---
TEST(ParserAnnexA051, NonAnsiWithPortDecls) {
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

}  // namespace
