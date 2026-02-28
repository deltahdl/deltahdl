// §29.10: Level-sensitive dominance

#include <gtest/gtest.h>

#include "simulator/udp_eval.h"

#include "builders_udp.h"

using namespace delta;

namespace {

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

}  // namespace
