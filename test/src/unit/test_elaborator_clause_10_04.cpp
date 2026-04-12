#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ProceduralAssignSim, InTaskBodyExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  task set_x();\n"
      "    x = 42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    set_x();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ProceduralAssignSim, InFunctionBodyExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function int compute();\n"
      "    int tmp;\n"
      "    tmp = 7 * 6;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = compute();\n"
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

TEST(ProceduralAssignSim, ProceduralAssignToNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
