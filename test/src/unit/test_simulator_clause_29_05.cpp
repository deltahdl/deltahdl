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

// Two rows share the same input pattern but name different current-state
// values; the matching row is selected by the UDP's internal state, proving
// the current-state field participates in the matching criterion.
TEST(UdpLevelSeq, CurrentStateDiscriminatesMatchingRow) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('0')
      .AddSeqRow({'0'}, '0', '1')
      .AddSeqRow({'0'}, '1', '-');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'0'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0'});
  EXPECT_EQ(state.GetOutput(), '1');
}

// Level-sensitive sequential UDPs inherit combinational matching, so inputs
// that match no row drive the output to x rather than hold the prior state.
TEST(UdpLevelSeq, UnmatchedInputsYieldX) {
  UdpBuilder b;
  b.SetSequential()
      .SetInitial('1')
      .AddSeqRow({'0'}, '?', '0')
      .AddSeqRow({'1'}, '?', '1');

  UdpEvalState state(b.decl);
  state.Evaluate({'x'});
  EXPECT_EQ(state.GetOutput(), 'x');
}

}  // namespace
