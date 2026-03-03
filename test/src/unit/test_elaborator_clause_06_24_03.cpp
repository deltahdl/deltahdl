// §6.24.3: Bit-stream casting

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.24.3: Bit-stream cast packs unpacked array elements MSB-first.
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
  // §6.24.3: index 0 occupies MSBs → 0xDEADBEEF.
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

}  // namespace
