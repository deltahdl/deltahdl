#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MinTypMaxElaboration, ContinuousAssignDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(1:2:3) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MinTypMaxElaboration, GateDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  and #(2:3:4) g1(c, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MinTypMaxElaboration, NetDeclDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  wire #(1:2:3) w = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MinTypMaxElaboration, MinExceedsTypAndMax) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(10:5:3) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MinTypMaxElaboration, GateDelayThreeSlotForwards) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  bufif0 #(1:2:3, 4:5:6, 7:8:9) g(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(mod->assigns[0].delay_fall->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(mod->assigns[0].delay_decay->kind, ExprKind::kMinTypMax);
}

}
