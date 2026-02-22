// §29.3.6: Summary of symbols

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

  UdpBuilder &SetCombinational() {
    decl.is_sequential = false;
    return *this;
  }

  UdpBuilder &AddRow(std::vector<char> inputs, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.output = output;
    decl.table.push_back(row);
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

TEST(UdpSymbols, WildcardQuestion) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '?'}, '0').AddRow({'1', '?'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'0', 'x'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'1', 'x'}), '1');
}

TEST(UdpSymbols, WildcardB) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'b', 'b'}, '1').AddRow({'x', '?'}, 'x');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'x', '0'}), 'x');
}

TEST(UdpSymbols, PosedgeSymbols) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'p'}, '?', '1')
      .AddSeqRow({'n'}, '?', '0');

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});

  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '0');

  state.EvaluateWithEdge({'x'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpSymbols, StarMatchesAnyChange) {
  UdpBuilder b;
  b.SetSequential().SetInitial('0').AddSeqRow({'*'}, '?', '-');

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});

  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');

  state.EvaluateWithEdge({'x'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '0');
}

}  // namespace
