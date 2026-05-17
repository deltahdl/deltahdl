#include <gtest/gtest.h>

#include "fixture_elaborator.h"

namespace {

// §28.3.4: "An optional name can be given to a gate or switch instance."
// Verify the elaborator accepts and lowers an unnamed gate instance to a
// continuous assignment exactly as it would for a named instance.
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
