// §29.5: Level-sensitive sequential UDPs

#include <gtest/gtest.h>

#include "builders_udp.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpLevelSeq, Latch) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'0', '?'}, '?', '-')
      .AddSeqRow({'1', '0'}, '?', '0')
      .AddSeqRow({'1', '1'}, '?', '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '0'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'1', '0'});
  EXPECT_EQ(state.GetOutput(), '0');
}

TEST(UdpLevelSeq, NoChange) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'0'}, '?', '-')
      .AddSeqRow({'1'}, '?', '1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'0'});
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0'});
  EXPECT_EQ(state.GetOutput(), '1');
}

}  // namespace
