// §29.9: Mixing level-sensitive and edge-sensitive descriptions

#include <gtest/gtest.h>

#include "simulation/udp_eval.h"

#include "builders_udp.h"

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

}  // namespace
