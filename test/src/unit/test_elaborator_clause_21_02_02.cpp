#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(IoStrobeElab, StrobeDoesNotCrash) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    $strobe(\"x=%d\", x);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
