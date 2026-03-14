#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §15.5: An event variable is created with is_event flag in the simulator.
TEST(IpcSync, EventVariableIsEventFlag) {
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev1", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* found = f.ctx.FindVariable("ev1");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_event);
}

// §15.5: A non-event variable does not have the is_event flag.
TEST(IpcSync, NonEventVariableFlagFalse) {
  SyncFixture f;
  auto* v = f.ctx.CreateVariable("x", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* found = f.ctx.FindVariable("x");
  ASSERT_NE(found, nullptr);
  EXPECT_FALSE(found->is_event);
}

// §15.5: Event declaration lowers with is_event set.
TEST(IpcSync, EventDeclarationLowersWithIsEvent) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_event);
}

// §15.5: Multiple event declarations each get is_event set.
TEST(IpcSync, MultipleEventDeclarationsLower) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_TRUE(va->is_event);
  EXPECT_TRUE(vb->is_event);
}

}  // namespace
