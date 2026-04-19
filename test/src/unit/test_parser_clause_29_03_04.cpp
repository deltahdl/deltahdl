#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpStateTable, UnspecifiedInputCombinationDefaultsToX) {
  auto r = Parse(
      "primitive partial(output out, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
}

// The state table must open with the `table` keyword; a UDP body that places
// rows directly after the port list is not a valid state table.
TEST(UdpStateTable, MissingTableKeywordRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  0 : 1;\n"
      "  1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The state table must be closed with `endtable`; running to end-of-file with
// no `endtable` is not a complete state table.
TEST(UdpStateTable, MissingEndtableKeywordRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n");
  EXPECT_TRUE(r.has_errors);
}

// Every row must end with a semicolon; running the next row's tokens straight
// after the output symbol is a malformed row.
TEST(UdpStateTable, RowMissingSemicolonRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Input field position i in a row corresponds to the i-th port identifier in
// the UDP header port list.
TEST(UdpStateTable, InputFieldOrderFollowsHeaderPortList) {
  auto r = Parse(
      "primitive gate(output y, input a, input b, input c);\n"
      "  table\n"
      "    0 1 0 : 0;\n"
      "    1 0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
  ASSERT_EQ(udp->table.size(), 2u);
  ASSERT_EQ(udp->table[0].inputs.size(), 3u);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '1');
  EXPECT_EQ(udp->table[0].inputs[2], '0');
}

// A combinational row carries one input field per input port plus a single
// output field separated from the inputs by a colon, with no current-state
// field.
TEST(UdpStateTable, CombinationalRowHasInputsAndOutputOnly) {
  auto r = Parse(
      "primitive and2(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs.size(), 2u);
  EXPECT_EQ(udp->table[0].current_state, 0);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].output, '1');
}

// A sequential row carries an additional current-state field between the
// inputs and the next-state output, delimited by colons on both sides.
TEST(UdpStateTable, SequentialRowHasInputsCurrentStateAndOutput) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : 1 : 0;\n"
      "    1 r : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs.size(), 2u);
  EXPECT_EQ(udp->table[0].current_state, '1');
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].current_state, '0');
  EXPECT_EQ(udp->table[1].output, '1');
}

// A row may describe at most one input transition; two parenthesized edge
// indicators in the same row is the example the LRM calls out as illegal.
TEST(UdpStateTable, TwoParenthesizedEdgeIndicatorsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) (10) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Two single-letter edge symbols in the same row likewise describe more than
// one input transition.
TEST(UdpStateTable, TwoSingleLetterEdgeSymbolsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b);\n"
      "  table\n"
      "    r f : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A single edge indicator is the common and legal case.
TEST(UdpStateTable, SingleEdgeIndicatorInRowAccepted) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// When every input field of a row is the literal x, the output field must also
// be x; specifying 0 instead is illegal.
TEST(UdpStateTable, AllXInputsWithZeroOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The all-x constraint applies even to a single-input UDP: x input with a 1
// output is illegal.
TEST(UdpStateTable, AllXInputsWithOneOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    x : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// An all-x input row with an x output is the legal way to express this case
// explicitly.
TEST(UdpStateTable, AllXInputsWithXOutputAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : x;\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Two rows with the same input combination but different outputs describe
// conflicting behavior for one input vector.
TEST(UdpStateTable, DuplicateInputsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive bad(output y, input a, input b);\n"
      "  table\n"
      "    0 1 : 0;\n"
      "    0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Sequential rows with the same inputs and current state but different
// next-state outputs are likewise conflicting.
TEST(UdpStateTable, SequentialDuplicateInputsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    0 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Two rows with identical inputs AND identical outputs are redundant but not
// conflicting; the LRM's rule targets differing outputs.
TEST(UdpStateTable, IdenticalDuplicateRowsNotFlagged) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
