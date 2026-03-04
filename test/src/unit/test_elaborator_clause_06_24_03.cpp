#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimCh6, BitStreamArrayToInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hDE;\n"
      "    arr[1] = 8'hAD;\n"
      "    arr[2] = 8'hBE;\n"
      "    arr[3] = 8'hEF;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(SimCh6, BitStreamShortArrayToInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 16'hCAFE;\n"
      "    arr[1] = 16'hBABE;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xCAFEBABEu);
}

}
