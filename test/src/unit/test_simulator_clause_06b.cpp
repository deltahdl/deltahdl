// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 30. type() from byte, assigned via expression from wider variable.
TEST(SimCh6b, TypeOpByteFromWiderAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  int wide;\n"
      "  initial begin\n"
      "    wide = 32'h12345678;\n"
      "    result = wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  // 0x12345678 truncated to 8 bits = 0x78.
  EXPECT_EQ(var->value.ToUint64(), 0x78u);
  EXPECT_TRUE(var->is_signed);
}

}  // namespace
