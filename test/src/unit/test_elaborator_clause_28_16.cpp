#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GateDelayElaboration, NoDelayLeavesAllSlotsNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(GateDelayElaboration, SingleDelayPopulatesRiseOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #5 g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
  EXPECT_EQ(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(GateDelayElaboration, TwoDelayPopulatesRiseAndFall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a, b;\n"
      "  or #(3, 7) g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 3u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 7u);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(GateDelayElaboration, ThreeDelayPopulatesAllSlots) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  bufif0 #(4, 6, 9) g(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 4u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 6u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 9u);
}

TEST(GateDelayElaboration, MultiOutputGateDelayAppliesToEveryOutput) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire o1, o2, in;\n"
      "  buf #(2, 4) g(o1, o2, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  for (size_t i = 0; i < 2; ++i) {
    ASSERT_NE(mod->assigns[i].delay, nullptr);
    EXPECT_EQ(mod->assigns[i].delay->int_val, 2u);
    ASSERT_NE(mod->assigns[i].delay_fall, nullptr);
    EXPECT_EQ(mod->assigns[i].delay_fall->int_val, 4u);
  }
}

TEST(GateDelayElaboration, MosSwitchDelayForwardsToContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire o, d, c;\n"
      "  nmos #(1, 2, 3) n1(o, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 1u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 2u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 3u);
}

TEST(GateDelayElaboration, CmosSwitchDelayForwardsToContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire o, d, nc, pc;\n"
      "  cmos #(7, 8, 9) c1(o, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 7u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 8u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 9u);
}

}  // namespace
