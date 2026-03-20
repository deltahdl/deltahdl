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

// --- Gate with delay elaborates normally ---
TEST(GateElaboration, GateWithDelayStillProducesAssign) {
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
