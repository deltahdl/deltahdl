// §29.6: Edge-sensitive sequential UDPs

#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulation/udp_eval.h"

using namespace delta;

namespace {

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder &SetSequential() {
    decl.is_sequential = true;
    return *this;
  }

  UdpBuilder &SetInitial(char val) {
    decl.has_initial = true;
    decl.initial_value = val;
    return *this;
  }

  UdpBuilder &AddSeqRow(std::vector<char> inputs, char state, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.current_state = state;
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};

TEST(UdpEdgeSeq, DFlipFlop) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('x')
      .AddSeqRow({'r', '0'}, '?', '0')
      .AddSeqRow({'r', '1'}, '?', '1')
      .AddSeqRow({'f', '?'}, '?', '-')
      .AddSeqRow({'?', '*'}, '?', '-');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), 'x');

  state.SetInputs({'0', '1'});

  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0', '1'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0', '0'}, 1, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'1', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');
}

}  // namespace
