// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 27. Verify .width and .ToUint64() for 32-bit int.
// ---------------------------------------------------------------------------
TEST(SimCh10, VerifyWidthAndToUint64_32bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int val;\n"
      "  initial begin\n"
      "    val = 32'hDEADBEEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// ---------------------------------------------------------------------------
// 28. Blocking assignment with ternary false branch.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignTernaryFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result = sel ? 42 : 99;\n"
      "  end\n"
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

// ---------------------------------------------------------------------------
// 29. Blocking assignment with modulo operator (%).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignModulo) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 17 % 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 17 % 5 = 2
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 30. Blocking assignment with unary plus (+).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignUnaryPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, result;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    result = +a;\n"
      "  end\n"
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

}  // namespace
