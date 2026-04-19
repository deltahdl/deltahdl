#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpInitialStatement, CapturesInitialValueOne) {
  auto r = Parse(
      "primitive srff(output reg q, input s, r);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

TEST(UdpInitialStatement, InitialOneDrivesOutputAtStart) {
  auto r = Parse(
      "primitive latch_init(output reg q, input d, en);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);

  EXPECT_EQ(eval.GetOutput(), '1');

  eval.Evaluate({'0', '0'});
  EXPECT_EQ(eval.GetOutput(), '1');
}

TEST(UdpInitialStatement, InitialZeroDrivesOutputAtStart) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '0'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '1'});
  EXPECT_EQ(state.GetOutput(), '0');
}

// The initial statement must assign to the output port. Assigning to an
// input port cannot set the output value at simulation start and shall be
// rejected.
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

// 1'bx is a single-bit literal and must be accepted and captured as an x
// initial value.
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

// An x initial value shall appear on the output at simulation start before
// any input transitions occur.
TEST(UdpInitialStatement, InitialXDrivesOutputAtStart) {
  auto r = Parse(
      "primitive latch_x(output reg q, input d, en);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.GetOutput(), 'x');
}

// The body of a UDP initial statement is a single procedural assignment,
// not a sequential block of statements.
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

// The assignment shall not be preceded by any delay control; the initial
// value is established at simulation start, before any time advances.
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

// Only the literal values 0, 1, and x (or their sized single-bit forms) are
// allowed as the RHS; an integer outside this set is illegal.
TEST(UdpInitialStatement, RejectsIntegerOutOfRangeRhs) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 2;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The single-bit sized form requires width 1; a wider sized literal does
// not represent a single-bit initial value.
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
