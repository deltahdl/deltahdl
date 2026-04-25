#include <gtest/gtest.h>

#include "builders_udp.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.10: when an edge-sensitive row and a level-sensitive row both match the
// same transition with conflicting outputs, the level-sensitive output wins.
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

// §29.10 edge case mirroring Table 29-3: the edge row resolves to a hold of
// the prior state while the level row resolves to a different explicit value.
// Dominance must still pick the level row's explicit value, not the edge
// row's held value.
TEST(UdpLevelDominance, LevelExplicitDominatesEdgeHold) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'f', '1'}, '?', '-')
      .AddSeqRow({'?', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'1', '1'});

  state.EvaluateWithEdge({'0', '1'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');
}

}  // namespace
