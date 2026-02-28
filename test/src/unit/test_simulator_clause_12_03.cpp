// §12.3: Syntax


#include "simulator/lowerer.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

// Sim test fixture
namespace {

// §12.3: statement_item dispatch — all statement kinds execute correctly
// (verifying the dispatcher works across multiple statement types in sequence)
TEST(SimA604, StmtItemDispatchMixed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"       // blocking_assignment
      "    if (a == 8'd1)\n"  // conditional_statement
      "      b = 8'd2;\n"
      "    begin\n"  // seq_block
      "      c = a + b;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

}  // namespace
