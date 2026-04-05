
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArrayAddressingElaboration, WriteAndReadArrayElement) {
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

TEST(ArrayAddressingElaboration, MultiDimArrayElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic [7:0] mem [0:3][0:3];\n"
      "  int result;\n"
      "  initial result = mem[1][2];\n"
      "endmodule\n"));
}

TEST(ArrayAddressingElaboration, MemoryIndirectionElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic [7:0] mem [0:7];\n"
      "  int result;\n"
      "  initial result = mem[mem[3]];\n"
      "endmodule\n"));
}

TEST(ArrayAddressingElaboration, BitSelectAfterArrayElementElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic result;\n"
      "  initial result = arr[2][5];\n"
      "endmodule\n"));
}

}  // namespace
