#include "fixture_simulator.h"
#include "fixture_specify.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SpecifyPathSim, SimpleParallelPathSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
