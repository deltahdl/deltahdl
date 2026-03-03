// §6.11.2: 2-state (two-value) and 4-state (four-value) data types

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

}  // namespace
