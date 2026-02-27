// §29.6: Edge-sensitive sequential UDPs

#include <gtest/gtest.h>

#include "simulation/udp_eval.h"

#include "builders_udp.h"

using namespace delta;

namespace {

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

}  // namespace
