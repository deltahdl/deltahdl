#include <gtest/gtest.h>

#include "builders_udp.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

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

TEST(UdpLevelDominance, JKFlipFlopWithPreset) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'r', '0', '0', '0'}, '?', '-')
      .AddSeqRow({'r', '1', '0', '0'}, '?', '1')
      .AddSeqRow({'r', '0', '1', '0'}, '?', '0')
      .AddSeqRow({'f', '?', '?', '0'}, '?', '-')
      .AddSeqRow({'?', '?', '?', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  state.SetInputs({'0', '0', '1', '0'});

  state.EvaluateWithEdge({'1', '0', '1', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '0');

  state.EvaluateWithEdge({'0', '0', '1', '1'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpLevelDominance, LevelOverridesEdge) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('x')
      .AddSeqRow({'r', '0'}, '?', '0')
      .AddSeqRow({'?', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'0', '1'});

  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

// Both an edge-sensitive and a level-sensitive row match the same input
// transition while specifying different outputs. The level-sensitive result
// shall dominate, not the edge-sensitive one.
TEST(UdpLevelDominance, LevelWinsWhenBothRowsMatchSameTransition) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('x')
      .AddSeqRow({'r', '1'}, '?', '0')
      .AddSeqRow({'?', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'0', '1'});

  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

// A level-sensitive row with '-' (hold) that matches alongside an edge row
// that would change the output still dominates: the output holds its
// previous value instead of taking the edge row's new value.
TEST(UdpLevelDominance, LevelHoldDominatesEdgeChange) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('1')
      .AddSeqRow({'r', '1'}, '?', '0')
      .AddSeqRow({'?', '1'}, '?', '-');

  UdpEvalState state(b.decl);
  state.SetInputs({'0', '1'});

  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

}  // namespace
