#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "preprocessor/preprocessor.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(SimCh50603, SystemTaskDoesNotConsumeTime) {
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

TEST(SimCh50603, SystemFunctionReturnsValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = $clog2(256);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 8u);
}

TEST(SimCh50603, SystemFunctionInExpression) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = $clog2(32) + $clog2(16);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 9u);
}
