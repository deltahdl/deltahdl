#include "fixture_parser.h"

using namespace delta;

// §29.7 Sequential UDP initialization.
//
// Table 29-2 and the surrounding prose constrain the *syntax* of a sequential
// UDP initial statement: its contents are limited to a single procedural
// assignment, the target shall be the reg that names the output port, the
// assigned value shall be one of 1'b1, 1'b0, 1'bx, 1, or 0, and delays are not
// permitted. The parser recognition and rejection of these forms lives in
// src/parser/parser_toplevel.cpp (ParseUdpDecl, the `initial` branch); §29.3.3
// owns that machinery and §29.7 restates the constraints in Table 29-2. These
// tests observe them at the parser stage. The simulation-start semantics live
// in test_simulator_clause_29_07.cpp.

namespace {

// Table 29-2 r3: 1'bx is a permitted value, and the parser captures it as the
// output's recorded start value.
TEST(UdpInitialStatement, CapturesInitialValueX) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1'bx;\n"
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

// Table 29-2 r3, unsized facet: a bare 0 or 1 is a permitted start value. This
// accept path is distinct from the sized 1'b? form above, so the parser must
// also recognize it and record the value.
TEST(UdpInitialStatement, AcceptsBareSingleBitLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

// Table 29-2 r2: the assignment shall target the reg that matches the output
// port; assigning to an input port is rejected.
TEST(UdpInitialStatement, RejectsInitialAssignmentToNonOutputPort) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial d = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Table 29-2 r1: the contents are limited to one procedural assignment; a
// begin/end block is not a plain assignment and is rejected.
TEST(UdpInitialStatement, RejectsBlockStatementInInitial) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial begin q = 1'b0; end\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// "Delays are not permitted in a UDP initial statement": a delay control before
// the assignment is rejected.
TEST(UdpInitialStatement, RejectsDelayBeforeAssignment) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial #5 q = 1'b1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Table 29-2 r3: a value outside the permitted single-bit set is rejected. A
// multi-bit sized literal is wider than the permitted single-bit values; this
// and the unsized out-of-range case both fall through the validator's single
// reject path, so one representative covers the rule.
TEST(UdpInitialStatement, RejectsMultiBitSizedLiteralRhs) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 2'b10;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
