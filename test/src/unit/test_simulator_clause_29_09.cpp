// §29.9: Mixing level-sensitive and edge-sensitive descriptions

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

TEST(UdpMixed, EdgeOnlyNoLevelOverride) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'r'}, '0', '1')
      .AddSeqRow({'r'}, '1', '0')
      .AddSeqRow({'f'}, '?', '-');

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});

  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');
}

}  // namespace
