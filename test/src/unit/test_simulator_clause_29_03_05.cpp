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

TEST(UdpInputZAsX, CombinationalXRowMatchesZ) {
  CombBuilder b;
  b.AddRow({'x', '0'}, '1').AddRow({'1', '1'}, '0');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'z', '0'}), '1');
}

TEST(UdpInputZAsX, CombinationalBRowRejectsCoercedZ) {
  CombBuilder b;
  b.AddRow({'b', '1'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'z', '1'}), 'x');
}

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

TEST(UdpInputZAsX, SetInputsCoercesZ) {
  CombBuilder b;
  b.AddRow({'x', 'x'}, '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'z', 'z'});
  EXPECT_EQ(state.Evaluate({'z', 'z'}), '1');
}

}  // namespace
