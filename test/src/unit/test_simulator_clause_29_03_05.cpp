#include <gtest/gtest.h>

#include <vector>

#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

struct CombBuilder {
  UdpDecl decl;

  CombBuilder& AddRow(std::vector<char> inputs, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};

// A z on an input symbol is observed as x, so a row expecting x on that
// position matches when the input is z.
TEST(UdpInputZAsX, CombinationalXRowMatchesZ) {
  CombBuilder b;
  b.AddRow({'x', '0'}, '1').AddRow({'1', '1'}, '0');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'z', '0'}), '1');
}

// '?' wildcard accepts 0/1/x; a z input should be coerced to x and still
// satisfy '?'.
TEST(UdpInputZAsX, CombinationalWildcardAcceptsZ) {
  CombBuilder b;
  b.AddRow({'?', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'z', '1'}), '1');
}

// 'b' matches only 0 or 1. Once z is coerced to x, the row should not
// match and the default x output should be produced.
TEST(UdpInputZAsX, CombinationalBRowRejectsCoercedZ) {
  CombBuilder b;
  b.AddRow({'b', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'z', '1'}), 'x');
}

// A posedge symbol 'p' accepts 0→1, 0→x, and x→1. Treating z as x means a
// 0→z transition (coerced to 0→x) satisfies 'p'.
TEST(UdpInputZAsX, SequentialEdgeZTreatedAsX) {
  UdpDecl decl;
  decl.is_sequential = true;
  decl.has_initial = true;
  decl.initial_value = '0';

  UdpTableRow row;
  row.inputs = {'p', '?'};
  row.current_state = '?';
  row.output = '1';
  decl.table.push_back(row);

  UdpEvalState state(decl);
  EXPECT_EQ(state.GetOutput(), '0');
  state.SetInputs({'0', '0'});
  state.EvaluateWithEdge({'z', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

// Previous value of z on the same input position is treated as x for edge
// detection. A z→0 transition is coerced to x→0, which negedge 'n' accepts.
TEST(UdpInputZAsX, SequentialPreviousZTreatedAsX) {
  UdpDecl decl;
  decl.is_sequential = true;
  decl.has_initial = true;
  decl.initial_value = '1';

  UdpTableRow row;
  row.inputs = {'n', '?'};
  row.current_state = '?';
  row.output = '0';
  decl.table.push_back(row);

  UdpEvalState state(decl);
  EXPECT_EQ(state.GetOutput(), '1');
  state.SetInputs({'z', '1'});
  state.EvaluateWithEdge({'0', '1'}, 0, 'z');
  EXPECT_EQ(state.GetOutput(), '0');
}

// SetInputs coerces z to x in the stored prev-inputs vector as well, so a
// subsequent Evaluate observes a stable-x rather than stable-z history.
TEST(UdpInputZAsX, SetInputsCoercesZ) {
  CombBuilder b;
  b.AddRow({'x', 'x'}, '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'z', 'z'});
  EXPECT_EQ(state.Evaluate({'z', 'z'}), '1');
}

}  // namespace
