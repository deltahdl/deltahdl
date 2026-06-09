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

// §29.4's multiplexer example points out that an input combination containing
// an x (its 0xx case) is simply absent from a table of literal rows, so the
// output becomes x. A literal row symbol never matches an x input, so the
// lookup falls through to the unknown value just like any other unlisted combo.
TEST(UdpCombinational, UnspecifiedCombinationWithXInputYieldsX) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0').AddRow({'1', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', 'x'}), 'x');
  EXPECT_EQ(state.Evaluate({'x', '1'}), 'x');
}

// §29.4 illustrates abbreviating a combinational table with the '?' symbol,
// noting that it stands for 0, 1, and x. Here a single row with a '?' in the
// last input position matches every one of those values, while the leading
// non-wildcard positions still demand an exact match.
TEST(UdpCombinational, WildcardQuestionMarkMatchesZeroOneAndX) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '1', '?'}, '1');
  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '1', 'x'}), '1');
  // A mismatch in a non-wildcard position is still unspecified -> x.
  EXPECT_EQ(state.Evaluate({'1', '1', '0'}), 'x');
}

TEST(UdpCombinational, OutputDependsOnlyOnCurrentInputs) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0').AddRow({'1', '1'}, '1');
  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
}

TEST(UdpCombinational, EmptyTableAlwaysReturnsX) {
  UdpBuilder b;
  b.SetCombinational();
  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0'}), 'x');
  EXPECT_EQ(state.Evaluate({'1'}), 'x');
}

}
