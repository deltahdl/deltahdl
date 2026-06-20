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

// §29.9: when an edge-sensitive row and a level-sensitive row both match the
// same input change but specify conflicting outputs, the level-sensitive case
// determines the result. Here the rising clock edge selects the edge row
// (output 0) while the steady second input selects the level row (output 1);
// both fire on the same transition and the level-sensitive output must win.
TEST(UdpLevelDominance, LevelOverridesEdge) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('x')
      .AddSeqRow({'r', '?'}, '?', '0')
      .AddSeqRow({'?', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  state.SetInputs({'0', '1'});

  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

// §29.9: edge-sensitive cases are processed before level-sensitive cases by
// kind, not by their position in the table. With the level row listed first and
// the edge row second, a simultaneous edge match still must not override the
// level-sensitive output. This guards against a "last matching row wins"
// resolution that would pass the edge-row-first case above.
TEST(UdpLevelDominance, LevelDominatesRegardlessOfTableOrder) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('x')
      .AddSeqRow({'?', '1'}, '?', '1')
      .AddSeqRow({'r', '?'}, '?', '0');

  UdpEvalState state(b.decl);
  state.SetInputs({'0', '1'});

  state.EvaluateWithEdge({'1', '1'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

}  // namespace
