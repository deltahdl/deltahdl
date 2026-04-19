#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder& SetCombinational() {
    decl.is_sequential = false;
    return *this;
  }

  UdpBuilder& AddRow(std::vector<char> inputs, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};

TEST(UdpCombinational, AndGate) {
  UdpBuilder b;
  b.SetCombinational()
      .AddRow({'0', '0'}, '0')
      .AddRow({'0', '1'}, '0')
      .AddRow({'1', '0'}, '0')
      .AddRow({'1', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
}

TEST(UdpCombinational, UnmatchedIsX) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0').AddRow({'1', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
}

// The default-x behavior holds for every unspecified combination, not just a
// single case.
TEST(UdpCombinational, EveryUnspecifiedCombinationYieldsX) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0');
  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '1'}), 'x');
}

// Specified rows continue to match after unspecified rows are queried — the
// default-x behavior does not overwrite the table.
TEST(UdpCombinational, SpecifiedRowsStillMatchAfterUnspecifiedQuery) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0').AddRow({'1', '1'}, '1');
  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
}

// Revisiting the same inputs produces the same output regardless of what was
// evaluated in between — the UDP holds no memory of prior inputs.
TEST(UdpCombinational, OutputDependsOnlyOnCurrentInputs) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0').AddRow({'1', '1'}, '1');
  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
}

// A table with no rows specifies no combination, so every evaluation falls
// through to the default-x output.
TEST(UdpCombinational, EmptyTableAlwaysReturnsX) {
  UdpBuilder b;
  b.SetCombinational();
  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0'}), 'x');
  EXPECT_EQ(state.Evaluate({'1'}), 'x');
}

}  // namespace
