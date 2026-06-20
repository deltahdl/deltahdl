#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ChandleDataType, ChandleNullDefault) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h == null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
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

TEST(ChandleDataType, ChandleBooleanTestNull) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
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

TEST(ChandleDataType, ChandleBooleanTestNonNull) {
  // §6.14: a chandle tested for a Boolean value yields 1 when it is not null.
  // A non-null value only arises through DPI, so seed the lowered variable
  // with a non-zero pointer value and observe the truthiness rule produce 1.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* handle = f.ctx.FindVariable("h");
  ASSERT_NE(handle, nullptr);
  handle->value = MakeLogic4VecVal(f.arena, 64, 0x1234u);

  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ChandleDataType, ChandleCaseEqualityNullSim) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h === null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
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

TEST(ChandleDataType, ChandleInequalityNullSim) {
  // §6.14: != is a valid chandle operator; a default (null) chandle compared
  // for inequality against null yields false at run time.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h != null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
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

TEST(ChandleDataType, ChandleCaseInequalityNullSim) {
  // §6.14: !== on a chandle has the same semantics as !=; a null chandle is
  // not case-unequal to null, so the test yields false.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h !== null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
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

TEST(ChandleDataType, ChandleChandleAssignSim) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle a, b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    b = a;\n"
      "    if (b == null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
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

}  // namespace
