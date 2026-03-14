#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §15.5.5.2: Event initialized to null has is_null_event flag set.
TEST(IpcSync, NullEventInitialization) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_null_event);
}

// §15.5.5.2: Triggering a null event has no effect.
TEST(IpcSync, TriggerNullEventHasNoEffect) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    -> ev;\n"
      "    result = 42;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §15.5.5.2: .triggered on a null event returns false.
TEST(IpcSync, NullEventTriggeredReturnsFalse) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "    result = ev.triggered ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §15.5.5.2: Imperative ev = null breaks the synchronization association.
TEST(IpcSync, ImperativeNullAssignmentBreaksAssociation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  initial begin\n"
      "    ev = null;\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_null_event);
}

// §15.5.5.2: Trigger after imperative null assignment has no effect.
TEST(IpcSync, TriggerAfterImperativeNullHasNoEffect) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    ev = null;\n"
      "    -> ev;\n"
      "    result = 99;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §15.5.5.2: Nullifying one alias does not affect the other.
TEST(IpcSync, NullAssignmentDoesNotAffectOtherAliases) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    a = null;\n"
      "    fork\n"
      "      begin @b; result = 77; end\n"
      "      begin #1 -> b; end\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
