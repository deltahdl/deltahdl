#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

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

TEST(GateDelayElaboration, GateDelayLoweredOntoContinuousAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and #7 g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.delay, nullptr);
  EXPECT_EQ(ca.delay->int_val, 7u);
  EXPECT_EQ(ca.delay_fall, nullptr);
  EXPECT_EQ(ca.delay_decay, nullptr);
}

}  // namespace
