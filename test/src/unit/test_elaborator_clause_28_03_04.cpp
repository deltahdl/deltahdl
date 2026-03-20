#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(GateDecl, ArrayRequiresName) {
  GateDeclInfo info;
  info.has_range = true;
  info.has_name = false;
  EXPECT_FALSE(ValidateGateDecl(info));
}

TEST(GateDecl, ArrayWithNameIsValid) {
  GateDeclInfo info;
  info.has_range = true;
  info.has_name = true;
  info.range_lhi = 0;
  info.range_rhi = 3;
  info.terminal_count = 3;
  EXPECT_TRUE(ValidateGateDecl(info));
}

// --- Unnamed gate elaborates the same as named ---
TEST(GateElaboration, UnnamedGateProducesAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  xor (y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca.rhs->op, TokenKind::kCaret);
}

}  // namespace
