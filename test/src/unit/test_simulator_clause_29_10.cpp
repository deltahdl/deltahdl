#include <gtest/gtest.h>

#include "builders_udp.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

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

}
