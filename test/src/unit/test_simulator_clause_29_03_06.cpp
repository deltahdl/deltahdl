#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder& SetSequential() {
    decl.is_sequential = true;
    return *this;
  }

  UdpBuilder& SetInitial(char val) {
    decl.has_initial = true;
    decl.initial_value = val;
    return *this;
  }

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

  UdpBuilder& AddSeqRow(std::vector<char> inputs, char state, char output) {
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

TEST(UdpSymbols, PotentialEdgeSymbols) {
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

// r is defined as (01): it fires on a clean 0→1 input transition and drives
// the sequential output to the row's next state.
TEST(UdpSymbols, RisingEdgeMatches01) {
  UdpBuilder b;
  b.SetSequential().SetInitial('0').AddSeqRow({'r'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});
  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

// r is strictly (01); a 0→x transition is a potential rising edge (p) but
// not a rising edge (r), so the r row does not match.
TEST(UdpSymbols, RisingEdgeDoesNotMatchPotentialRise) {
  UdpBuilder b;
  b.SetSequential().SetInitial('0').AddSeqRow({'r'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});
  state.EvaluateWithEdge({'x'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), 'x');
}

// f is defined as (10): it fires on a clean 1→0 input transition.
TEST(UdpSymbols, FallingEdgeMatches10) {
  UdpBuilder b;
  b.SetSequential().SetInitial('1').AddSeqRow({'f'}, '?', '0');

  UdpEvalState state(b.decl);
  state.SetInputs({'1'});
  state.EvaluateWithEdge({'0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '0');
}

// A parenthesized (vw) edge matches exactly when the previous input equals v
// and the new input equals w.
TEST(UdpSymbols, ParenthesizedEdgeMatchesExactTransition) {
  UdpDecl decl;
  decl.is_sequential = true;
  decl.has_initial = true;
  decl.initial_value = '0';
  UdpTableRow row;
  row.inputs = {'\x01'};
  row.paren_edges = {{'0', 'x'}};
  row.current_state = '?';
  row.output = '1';
  decl.table.push_back(row);

  UdpEvalState state(decl);
  state.SetInputs({'0'});
  state.EvaluateWithEdge({'x'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

// A (vw) edge does not match when the observed transition differs from v→w
// on either endpoint.
TEST(UdpSymbols, ParenthesizedEdgeRejectsNonMatchingTransition) {
  UdpDecl decl;
  decl.is_sequential = true;
  decl.has_initial = true;
  decl.initial_value = '0';
  UdpTableRow row;
  row.inputs = {'\x01'};
  row.paren_edges = {{'0', 'x'}};
  row.current_state = '?';
  row.output = '1';
  decl.table.push_back(row);

  UdpEvalState state(decl);
  state.SetInputs({'0'});
  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), 'x');
}

}  // namespace
