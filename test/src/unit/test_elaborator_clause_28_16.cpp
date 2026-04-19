#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §28.16 R3: with no `#` spec on the gate, the lowered continuous-assign
// carries null delay exprs in all three slots — the simulator then treats
// missing delays as zero.
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

// §28.16 R4: a single delay on a gate instance reaches the cont-assign in
// the rise slot only; the other two slots stay null so the simulator
// reuses the single value for every transition.
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

// §28.16 R5: two-delay form must surface both values so the simulator can
// pick rise vs. fall per Table 28-9; turn-off stays null.
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

// §28.16 R6: three-delay form on a delay3-capable gate must surface all
// three exprs so rise / fall / turn-off map to their Table 28-9 slots.
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

// §28.16 R1: a delay on a multi-output buf/not gate must apply to every
// output — the gate emits one cont-assign per output, and all of them
// must carry the same delay triple.
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

// §28.16 R1 (MOS path): the MOS lowering path builds a ternary RHS but
// must still forward the gate's delay spec to its cont-assign. Guards
// against regressions where the pass-switch lowering silently drops
// delays.
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

// §28.16 R1 (CMOS path): cmos lowers to a nested ternary and, like the
// MOS path above, must still forward its `#(d1, d2, d3)` spec. Covers
// the second unique lowering path for switch-style gates.
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
