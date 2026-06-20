#include <gtest/gtest.h>

#include "builders_udp.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.6: edge-sensitive behavior triggers output changes on specific input
// transitions, so the state table becomes a transition table. A rising-edge
// D flip-flop expressed with single-letter edge symbols.
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

// §29.6: all unspecified transitions default the output to x. The only row
// here captures a rising edge; a falling edge matches nothing and yields x.
TEST(UdpEdgeSeq, UnspecifiedEdgeYieldsX) {
  UdpBuilder b;
  b.SetSequential().SetInitial('1').AddSeqRow({'r'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'1'});

  state.EvaluateWithEdge({'0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), 'x');
}

// §29.6: a transition is specified by a pair of values in parentheses such as
// (01), which denotes a transition from 0 to 1. This is the rising-edge D
// flip-flop written with parenthesized edge transitions (clock on input 0,
// data on input 1) and exercises the parenthesized-edge match path.
TEST(UdpEdgeSeq, ParenthesizedEdgeTransitions) {
  // Edge on the clock input (input 0), level symbol on data (input 1).
  auto clk_edge = [](char from, char to, char data, char cur, char out) {
    UdpTableRow row;
    row.inputs = {'\x01', data};
    row.paren_edges = {{from, to}, {0, 0}};
    row.current_state = cur;
    row.output = out;
    return row;
  };

  UdpDecl decl;
  decl.is_sequential = true;
  decl.table.push_back(clk_edge('0', '1', '0', '?', '0'));  // (01) 0 : ? : 0
  decl.table.push_back(clk_edge('0', '1', '1', '?', '1'));  // (01) 1 : ? : 1
  decl.table.push_back(clk_edge('0', '?', '1', '1', '1'));  // (0?) 1 : 1 : 1
  decl.table.push_back(clk_edge('0', '?', '0', '0', '0'));  // (0?) 0 : 0 : 0
  decl.table.push_back(clk_edge('?', '0', '?', '?', '-'));  // (?0) ? : ? : -
  // Edge on the data input (input 1): ? (??) : ? : -
  {
    UdpTableRow row;
    row.inputs = {'?', '\x01'};
    row.paren_edges = {{0, 0}, {'?', '?'}};
    row.current_state = '?';
    row.output = '-';
    decl.table.push_back(row);
  }

  UdpEvalState state(decl);
  state.SetInputs({'0', '1'});

  // (01) with data 1 captures a 1: the parenthesized 0->1 transition fires.
  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  // §29.6: a clock transition of 0->x with data 0 and current state 1 leaves no
  // matching row, so the output goes to x.
  state.EvaluateWithEdge({'x', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), 'x');
}

}  // namespace
