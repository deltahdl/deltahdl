// Tests for §29 User-defined primitives — runtime evaluation.
// Covers combinational lookup, sequential state, edge detection,
// and §29.10 level-sensitive dominance.

#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulation/udp_eval.h"

using namespace delta;

namespace {

// =============================================================================
// Helper: build a UdpDecl with a table.
// =============================================================================

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder& SetCombinational() {
    decl.is_sequential = false;
    return *this;
  }

  UdpBuilder& SetSequential() {
    decl.is_sequential = true;
    return *this;
  }

  UdpBuilder& SetInitial(char val) {
    decl.has_initial = true;
    decl.initial_value = val;
    return *this;
  }

  // Add a combinational row: inputs -> output.
  UdpBuilder& AddRow(std::vector<char> inputs, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }

  // Add a sequential row: inputs, current_state -> next_state.
  UdpBuilder& AddSeqRow(std::vector<char> inputs, char state, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.current_state = state;
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};

// =============================================================================
// §29.4 Combinational UDP evaluation
// =============================================================================

TEST(UdpEval, CombinationalAndGate) {
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

TEST(UdpEval, CombinationalUnmatchedIsX) {
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '0'}, '0').AddRow({'1', '1'}, '1');

  UdpEvalState state(b.decl);
  // (0,1) and (1,0) are unmatched -> x
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
}

TEST(UdpEval, CombinationalWildcardQuestion) {
  // ? matches 0, 1, x
  UdpBuilder b;
  b.SetCombinational().AddRow({'0', '?'}, '0').AddRow({'1', '?'}, '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'0', 'x'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'1', 'x'}), '1');
}

TEST(UdpEval, CombinationalWildcardB) {
  // b matches 0, 1 (not x)
  UdpBuilder b;
  b.SetCombinational().AddRow({'b', 'b'}, '1').AddRow({'x', '?'}, 'x');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'x', '0'}), 'x');
}

// =============================================================================
// §29.5 Level-sensitive sequential UDP
// =============================================================================

TEST(UdpEval, SequentialLatch) {
  // Transparent latch: when enable=1, q follows data; when enable=0, hold.
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'0', '?'}, '?', '-')   // enable=0: hold
      .AddSeqRow({'1', '0'}, '?', '0')   // enable=1, data=0: q=0
      .AddSeqRow({'1', '1'}, '?', '1');  // enable=1, data=1: q=1

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');  // initial value

  state.Evaluate({'1', '1'});  // enable=1, data=1 -> q=1
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '1'});  // enable=0 -> hold q=1
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '0'});  // enable=0, data changes -> still hold
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'1', '0'});  // enable=1, data=0 -> q=0
  EXPECT_EQ(state.GetOutput(), '0');
}

TEST(UdpEval, SequentialNoChange) {
  // '-' in output means no change.
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'0'}, '?', '-')   // input=0: no change
      .AddSeqRow({'1'}, '?', '1');  // input=1: set to 1

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'0'});  // no change
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1'});  // set to 1
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0'});  // no change (still 1)
  EXPECT_EQ(state.GetOutput(), '1');
}

// =============================================================================
// §29.6 Edge-sensitive sequential UDP
// =============================================================================

TEST(UdpEval, EdgeSensitiveDFlipFlop) {
  // D flip-flop: captures data on rising edge of clock.
  // Table entries use edge specifiers on the clock input.
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('x')
      // Rising edge, data=0: output=0
      .AddSeqRow({'r', '0'}, '?', '0')
      // Rising edge, data=1: output=1
      .AddSeqRow({'r', '1'}, '?', '1')
      // Any other change: no change
      .AddSeqRow({'f', '?'}, '?', '-')
      .AddSeqRow({'?', '*'}, '?', '-');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), 'x');

  // Set initial inputs: clk=0, data=1
  state.SetInputs({'0', '1'});

  // Rising edge on clk: 0->1, data=1 -> capture 1
  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  // Falling edge on clk: 1->0 -> no change
  state.EvaluateWithEdge({'0', '1'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  // Change data while clk=0 -> no change
  state.EvaluateWithEdge({'0', '0'}, 1, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  // Rising edge, data=0 -> capture 0
  state.EvaluateWithEdge({'1', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');
}

// =============================================================================
// §29.9 / §29.10 Level-sensitive dominance
// =============================================================================

TEST(UdpEval, LevelSensitiveDominance) {
  // JK flip-flop with async preset.
  // Edge-sensitive: rising clock captures J/K.
  // Level-sensitive: preset=1 forces output=1 regardless.
  // Per §29.10, level-sensitive dominates when both match.
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      // Edge-sensitive: rising clock, J=0,K=0 -> no change
      .AddSeqRow({'r', '0', '0', '0'}, '?', '-')
      // Edge-sensitive: rising clock, J=1,K=0 -> set
      .AddSeqRow({'r', '1', '0', '0'}, '?', '1')
      // Edge-sensitive: rising clock, J=0,K=1 -> reset
      .AddSeqRow({'r', '0', '1', '0'}, '?', '0')
      // Falling clock: no change
      .AddSeqRow({'f', '?', '?', '0'}, '?', '-')
      // Level-sensitive: preset=1 -> force output=1
      .AddSeqRow({'?', '?', '?', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  // Clock=0, J=0, K=1, preset=0
  state.SetInputs({'0', '0', '1', '0'});

  // Rising clock edge with K=1, preset=0 -> edge says reset to 0
  state.EvaluateWithEdge({'1', '0', '1', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');

  // Now: falling clock edge AND preset=1 simultaneously.
  // Edge-sensitive: falling clock -> no change (output stays 0)
  // Level-sensitive: preset=1 -> force 1
  // §29.10: Level-sensitive dominates -> output = 1
  state.EvaluateWithEdge({'0', '0', '1', '1'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpEval, LevelDominanceOverridesEdge) {
  // Simpler test: edge entry says '0', level entry says '1'.
  // Level wins.
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('x')
      // Edge-sensitive: rising edge on input 0 -> output 0
      .AddSeqRow({'r', '0'}, '?', '0')
      // Level-sensitive: input 1 = 1 -> output 1
      .AddSeqRow({'?', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'0', '1'});

  // Rising edge on input 0, input 1 = 1
  // Edge says: 0
  // Level says: 1 (because input 1 = 1)
  // Level dominates -> 1
  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpEval, EdgeOnlyNoLevelOverride) {
  // When only edge-sensitive matches, its result stands.
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      // Edge-sensitive: rising edge -> toggle
      .AddSeqRow({'r'}, '0', '1')
      .AddSeqRow({'r'}, '1', '0')
      // Falling: no change
      .AddSeqRow({'f'}, '?', '-');

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});

  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');  // falling: no change

  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');  // toggle back
}

// =============================================================================
// Edge symbol matching
// =============================================================================

TEST(UdpEval, PosedgeSymbols) {
  // 'p' matches (01), (0x), (x1)
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'p'}, '?', '1')
      .AddSeqRow({'n'}, '?', '0');

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});

  // 0->1 is a positive edge
  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  // 1->0 is a negative edge
  state.EvaluateWithEdge({'0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '0');

  // 0->x: potential positive edge (p matches)
  state.EvaluateWithEdge({'x'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpEval, StarMatchesAnyChange) {
  // '*' = (??) matches any transition
  UdpBuilder b;
  b.SetSequential().SetInitial('0').AddSeqRow({'*'}, '?',
                                              '-');  // any change -> no change

  UdpEvalState state(b.decl);
  state.SetInputs({'0'});

  state.EvaluateWithEdge({'1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');  // no change

  state.EvaluateWithEdge({'x'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '0');  // no change
}

// =============================================================================
// Initial value
// =============================================================================

TEST(UdpEval, InitialValueDefault) {
  UdpBuilder b;
  b.SetSequential();
  // No initial value set -> default x

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), 'x');
}

TEST(UdpEval, InitialValueOne) {
  UdpBuilder b;
  b.SetSequential().SetInitial('1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '1');
}

}  // namespace
