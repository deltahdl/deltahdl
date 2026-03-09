
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(VarLvalueMultiDimArray, VarLvalueMultiDimArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin mem[0] = 8'h00; mem[2] = 8'hAB; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("mem[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

}  // namespace
