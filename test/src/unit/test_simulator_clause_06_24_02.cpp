#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DynamicCastSim, CastEnumSuccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = $cast(c, 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
}

TEST(DynamicCastSim, CastEnumTaskValid) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial begin\n"
      "    $cast(c, 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 2u);
}

TEST(DynamicCastSim, CastEnumInCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int flag;\n"
      "  initial begin\n"
      "    flag = 0;\n"
      "    if ($cast(c, 1))\n"
      "      flag = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

TEST(DynamicCastSim, TaskFormInvalidLeavesDestUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial begin\n"
      "    $cast(c, 1);\n"
      "    $cast(c, 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
}

TEST(DynamicCastSim, TaskFormInvalidRaisesRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial begin\n"
      "    $cast(c, 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(DynamicCastSim, TaskFormValidRaisesNoError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial begin\n"
      "    $cast(c, 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DynamicCastSim, FunctionFormInvalidRaisesNoError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = $cast(c, 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.FindVariable("ok")->value.ToUint64(), 0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DynamicCastSim, FunctionFormInvalidPreservesDestValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    $cast(c, 1);\n"
      "    ok = $cast(c, 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 0u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
}

TEST(DynamicCastSim, FunctionFormInvalidConditionNotTaken) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int flag;\n"
      "  initial begin\n"
      "    flag = 0;\n"
      "    if ($cast(c, 10))\n"
      "      flag = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
}

TEST(DynamicCastSim, CastEnumWithExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = $cast(c, 1 + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 2u);
}

TEST(DynamicCastSim, CastEnumFirstMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    $cast(c, 2);\n"
      "    ok = $cast(c, 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 0u);
}

// §6.24.2: casting between cast-compatible singular (integral) operands is a
// valid assignment, so the function form assigns the destination and returns 1.
// Exercises the success path for a non-enum destination.
TEST(DynamicCastSim, FunctionFormIntegralCastSucceeds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = $cast(d, 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 5u);
}

// §6.24.2: the task form of a valid integral cast assigns the destination and,
// because the assignment is valid, raises no run-time error.
TEST(DynamicCastSim, TaskFormIntegralCastAssignsNoError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d;\n"
      "  initial begin\n"
      "    $cast(d, 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 5u);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
