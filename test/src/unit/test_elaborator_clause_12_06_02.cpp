// §12.6.2: Pattern matching in if statements


#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §12.6.2: matches operator in if-condition elaborates
TEST(ElabA60701, MatchesInIfElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    if (x matches 8'd3) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
