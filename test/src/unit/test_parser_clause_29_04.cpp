// §29.4: Combinational UDPs

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.5 -- UDP declarations
// =============================================================================
TEST(ParserAnnexA, A5UdpCombinational) {
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

// =============================================================================
// A.5.1 -- UDP declaration
//
// udp_nonansi_declaration ::=
//   { attribute_instance } primitive udp_identifier ( udp_port_list ) ;
//
// udp_ansi_declaration ::=
//   { attribute_instance } primitive udp_identifier
//     ( udp_declaration_port_list ) ;
//
// udp_declaration ::=
//   udp_nonansi_declaration udp_port_declaration { udp_port_declaration }
//     udp_body endprimitive [ : udp_identifier ]
//   | udp_ansi_declaration udp_body
//     endprimitive [ : udp_identifier ]
//   | extern udp_nonansi_declaration
//   | extern udp_ansi_declaration
//   | { attribute_instance } primitive udp_identifier ( . * ) ;
//     { udp_port_declaration } udp_body
//     endprimitive [ : udp_identifier ]
// =============================================================================
// --- udp_ansi_declaration: combinational ---
TEST(ParserAnnexA051, AnsiCombinational) {
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

// --- udp_declaration: multiple UDPs in compilation unit ---
TEST(ParserAnnexA051, MultipleUdps) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive buf2(output out, input in);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_EQ(r.cu->udps[1]->name, "buf2");
}

// --- udp_declaration: single input UDP ---
TEST(ParserAnnexA051, SingleInput) {
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

// =============================================================================
// Simulation tests -- UDP evaluation (covers A.5.1 declaration semantics)
// =============================================================================
// --- Combinational UDP evaluation ---
TEST(ParserAnnexA051, SimCombinationalEval) {
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
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
}

// =============================================================================
// A.5.3 -- UDP body (part a: productions 1-8)
//
// udp_body ::= combinational_body | sequential_body
// combinational_body ::= table combinational_entry { combinational_entry }
//                         endtable
// combinational_entry ::= level_input_list : output_symbol ;
// sequential_body ::= [ udp_initial_statement ] table sequential_entry
//                     { sequential_entry } endtable
// udp_initial_statement ::= initial output_port_identifier = init_val ;
// init_val ::= 1'b0 | 1'b1 | 1'bx | 1'bX | 1'B0 | 1'B1 | 1'Bx | 1'BX
//              | 1 | 0
// sequential_entry ::= seq_input_list : current_state : next_state ;
// seq_input_list ::= level_input_list | edge_input_list
// =============================================================================
// ---------------------------------------------------------------------------
// Production 1: udp_body ::= combinational_body | sequential_body
// ---------------------------------------------------------------------------
// udp_body alternative 1: combinational_body
TEST(ParserAnnexA053, UdpBody_CombinationalAlternative) {
  auto r = Parse(
      "primitive and_gate(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  EXPECT_EQ(udp->table.size(), 4);
}

// Simulation: combinational body evaluates correctly
TEST(ParserAnnexA053, UdpBody_SimCombinational) {
  auto r = Parse(
      "primitive or_gate(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(eval.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(eval.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(eval.Evaluate({'1', '1'}), '1');
}

}  // namespace
