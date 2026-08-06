#include "fixture_parser.h"

using namespace delta;

// §29.3.3 Sequential UDP initial statement.
//
// The clause text defines the *syntax* of the sequential UDP initial
// statement: it begins with the `initial` keyword and the following statement
// shall be an assignment of a single-bit literal value to the output port. The
// statement records the value the output takes when simulation begins; the
// simulation-start mechanics themselves belong to §29.7 (Sequential UDP
// initialization), so this clause is observed entirely at the parser stage in
// src/parser/parser_toplevel.cpp (ParseUdpDecl).

namespace {

// S2 + value capture: the statement begins with `initial`, and the parser
// captures the single-bit literal the output assumes at simulation start.
TEST(UdpSequentialInitial, InitialKeywordIntroducesAssignment) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

// init_val bare-literal form: 0 and 1 are accepted single-bit literals, a
// distinct grammar branch from the sized 1'b? forms.
TEST(UdpSequentialInitial, BareZeroAndOneAreSingleBitLiterals) {
  auto r0 = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r0.cu, nullptr);
  EXPECT_FALSE(r0.has_errors);
  EXPECT_EQ(r0.cu->udps[0]->initial_value, '0');

  auto r1 = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r1.cu, nullptr);
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.cu->udps[0]->initial_value, '1');
}

// S3 facet "single-bit literal value": the value may be the unknown state x.
// §29.2 gives the output three states (0, 1, x), so the initial statement must
// admit an x-valued single-bit literal, distinct from the 0/1 forms.
TEST(UdpSequentialInitial, UnknownSingleBitLiteralIsAccepted) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->has_initial);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

// S3 facet "single-bit literal value": the capital base letter and capital
// value digit form the same single-bit literal, a distinct lexical branch that
// the parser accepts and folds to the same captured value.
TEST(UdpSequentialInitial, CapitalBaseAndDigitSingleBitLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'B1;\n"
      "  table\n"
      "    0 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

// S3 facet "single-bit literal value": the sized form carrying value 0. This
// exercises the sized-base branch with a 0 digit, distinct from the bare `0`
// literal branch and from the sized value-1 form.
TEST(UdpSequentialInitial, SizedZeroSingleBitLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

// S3 facet "single-bit literal value": an upper-case X value digit denotes the
// same unknown state as lower-case x. This exercises the value-capture path
// that folds the upper-case digit down to the canonical 'x'.
TEST(UdpSequentialInitial, UpperCaseUnknownDigitFoldsToX) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'bX;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

// S3 facet "literal": the value must be a literal, so a named reference on the
// right-hand side (not one of the accepted literal forms) is rejected.
TEST(UdpSequentialInitial, NonLiteralValueIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = seed;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// S3 facet "to the output port": the assignment target must be the output
// port, not an input.
TEST(UdpSequentialInitial, AssignmentMustTargetOutputPort) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial d = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// S3 facet "single-bit literal value": a multi-bit literal is rejected.
TEST(UdpSequentialInitial, MultiBitLiteralIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 2'b10;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// S3 facet "an assignment statement": a procedural block is not a plain
// assignment and is rejected.
TEST(UdpSequentialInitial, BlockStatementIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial begin q = 1'b0; end\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
