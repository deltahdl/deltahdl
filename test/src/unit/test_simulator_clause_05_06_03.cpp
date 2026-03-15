#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(SystemNameSim, SystemTaskDoesNotConsumeTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd1;\n"
      "    $display(\"msg\");\n"
      "    result = result + 8'd2;\n"
      "    $display(\"msg2\");\n"
      "    result = result + 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(SystemNameSim, SystemFunctionReturnsValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = $clog2(256);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 8u);
}

TEST(SystemNameSim, MultipleSystemTasksNoTimeConsumption) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    $display(\"a=%0d\", a);\n"
      "    $display(\"b=%0d\", b);\n"
      "    $display(\"done\");\n"
      "    b = a + 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(SystemNameSim, SystemFunctionInExpression) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = $clog2(32) + $clog2(16);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 9u);
}

TEST(SystemNameSim, SystemTaskInFunctionBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  function void set_result;\n"
      "    $display(\"called\");\n"
      "    result = 8'd42;\n"
      "  endfunction\n"
      "  initial set_result();\n"
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

TEST(SystemNameSim, SystemFunctionWithDataTypeArg) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = $bits(logic [7:0]);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 8u);
}
