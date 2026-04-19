#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §28.16.1 R1: a cont-assign with a mintypmax delay must elaborate — the
// elaborator forwards the kMinTypMax node unchanged to the RtlirContAssign
// delay slot; there is no ordering validator (R2 forbids one).
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

// §28.16.1 R1: a gate-instance mintypmax delay must ride through gate
// lowering to the RtlirContAssign delay slot without being reduced.
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

// §28.16.1 R1: a net declaration with a mintypmax delay on a driven net
// must elaborate — the net_delay must forward to the cont-assign lowered
// for the net, carrying the kMinTypMax node through.
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

// §28.16.1 R2: the elaborator must not reject a mintypmax spec whose min
// value exceeds typ or max — there is no ordering invariant to enforce,
// so any three expressions are acceptable.
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

// §28.16.1 R1: a three-slot gate mintypmax spec must surface all three
// slots to the RtlirContAssign (delay, delay_fall, delay_decay) with a
// kMinTypMax node in each — this is the shape the simulator reads to run
// DelayMode selection per slot.
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

}  // namespace
