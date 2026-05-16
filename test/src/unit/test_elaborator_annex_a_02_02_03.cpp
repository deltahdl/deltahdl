#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- delay_value: identifier elaboration ---

TEST(DelayElaboration, DelayValueParameterIdentifier) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter D = 5;\n"
      "  wire w;\n"
      "  assign #D w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->kind, ExprKind::kIdentifier);
}

// --- delay_value: real number ---

TEST(DelayElaboration, DelayValueRealElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign #1.5 w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->kind, ExprKind::kRealLiteral);
}

// --- delay_value: time_literal elaboration ---

TEST(DelayElaboration, ContAssignTimeLiteralDelay) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign #10ns w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->kind, ExprKind::kTimeLiteral);
}

// --- delay_value: unsigned_number elaboration ---

TEST(DelayElaboration, DelayValueUnsignedNumberElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign #5 w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
}

// --- delay_value: 1step elaboration ---

TEST(DelayElaboration, DelayValueOneStepElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign #1step w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->text, "1step");
}

}  // namespace
