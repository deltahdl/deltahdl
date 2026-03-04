#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(GateDecl, MaxDelaysByGateType) {
  struct {
    GateType gate;
    uint32_t expected;
  } const kCases[] = {
      {GateType::kPullup, 0u}, {GateType::kPulldown, 0u}, {GateType::kAnd, 2u},
      {GateType::kBufif0, 3u}, {GateType::kNmos, 3u},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(MaxDelays(c.gate), c.expected);
  }
}

}
