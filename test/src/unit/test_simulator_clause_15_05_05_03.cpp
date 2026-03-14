#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §15.5.5.3: Two distinct events compare not-equal.
TEST(IpcSync, DistinctEventsCompareNotEqual) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (a == b) ? 1 : 0;\n"
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

// §15.5.5.3: Merged events compare equal (same sync queue).
TEST(IpcSync, MergedEventsCompareEqual) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    result = (a == b) ? 1 : 0;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.5.3: Event != null returns true for non-null event.
TEST(IpcSync, EventNotEqualToNullReturnsTrue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev != null) ? 1 : 0;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.5.3: Event == null returns true for null event.
TEST(IpcSync, NullEventEqualsNull) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev == null) ? 1 : 0;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.5.3: Case equality (===) has same semantics as == for events.
TEST(IpcSync, CaseEqualitySameSemanticsAsEqForEvents) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    result = (a === b) ? 1 : 0;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.5.3: Case inequality (!==) has same semantics as != for events.
TEST(IpcSync, CaseInequalitySameSemanticsAsNeqForEvents) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (a !== b) ? 1 : 0;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.5.3: Boolean conversion — non-null event is truthy.
TEST(IpcSync, NonNullEventIsTruthy) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = ev ? 1 : 0;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.5.3: Boolean conversion — null event is falsy.
TEST(IpcSync, NullEventIsFalsy) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = ev ? 1 : 0;\n"
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

}  // namespace
