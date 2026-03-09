#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimA609, SystemTaskDisplay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(FormatArg, HexLeadingZeros) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0x0A);

  EXPECT_EQ(FormatArg(val, 'h'), "0a");
}

TEST(FormatArg, OctalLeadingZeros) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 5);

  EXPECT_EQ(FormatArg(val, 'o'), "005");
}

TEST(FormatArg, BinaryReturnsToString) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 4, 0b1010);
  EXPECT_EQ(FormatArg(val, 'b'), "1010");
}

}
