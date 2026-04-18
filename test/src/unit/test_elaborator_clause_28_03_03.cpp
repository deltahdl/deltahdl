#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(GateDelayValidity, MaxDelaysByGateType) {
  // Every gate type in Table 28-4 is covered so any edit to MaxDelays
  // surfaces immediately as a test failure.
  struct {
    GateType gate;
    uint32_t expected;
  } const kCases[] = {
      // Pull gates: no delay spec.
      {GateType::kPullup, 0u},
      {GateType::kPulldown, 0u},
      // Pass switches: no delay spec.
      {GateType::kTran, 0u},
      {GateType::kRtran, 0u},
      // N-input gates: up to 2 delays.
      {GateType::kAnd, 2u},
      {GateType::kNand, 2u},
      {GateType::kOr, 2u},
      {GateType::kNor, 2u},
      {GateType::kXor, 2u},
      {GateType::kXnor, 2u},
      // N-output gates: up to 2 delays.
      {GateType::kBuf, 2u},
      {GateType::kNot, 2u},
      // Enable gates: up to 3 delays.
      {GateType::kBufif0, 3u},
      {GateType::kBufif1, 3u},
      {GateType::kNotif0, 3u},
      {GateType::kNotif1, 3u},
      // MOS / CMOS switches: up to 3 delays.
      {GateType::kNmos, 3u},
      {GateType::kPmos, 3u},
      {GateType::kRnmos, 3u},
      {GateType::kRpmos, 3u},
      {GateType::kCmos, 3u},
      {GateType::kRcmos, 3u},
      // Pass-enable switches: up to 2 delays.
      {GateType::kTranif0, 2u},
      {GateType::kTranif1, 2u},
      {GateType::kRtranif0, 2u},
      {GateType::kRtranif1, 2u},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(MaxDelays(c.gate), c.expected);
  }
}

// --- Gate with delay elaborates normally ---
TEST(GateDelayElaboration, GateWithDelayStillProducesAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  or #10 g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca.rhs->op, TokenKind::kPipe);
}

}  // namespace
