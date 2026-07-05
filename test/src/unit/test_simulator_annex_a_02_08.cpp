#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

// §A.2.8 end-to-end coverage. The sole production of §A.2.8,
// block_item_declaration, is syntactic: it states that a data_declaration
// (§A.2.1.3), a local_parameter_declaration or parameter_declaration
// (§A.2.1.1), or a let_declaration (§A.2.12) may appear as an item of a
// procedural block. These tests build each admitted alternative from its
// dependency's real source syntax as a block item inside an initial block,
// then run the design and observe the declared entity carrying a value into a
// module signal — i.e. observe the parsed/elaborated/lowered block item being
// consumed by production code, not merely accepted by the parser.
//
// The let_declaration alternative is exercised only at parse/elaborate depth
// (see the parser and elaborator canonical files): a block-scope let has no
// runtime expansion path, so it is not driven through the simulator here.

namespace {

// Alt 1: a data_declaration block item. A plain variable declared inside the
// block holds an intermediate value that flows into the observed module signal.
TEST(BlockItemDeclSim, DataDeclBlockItemProducesRuntimeValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    int tmp;\n"
      "    tmp = 8'd40;\n"
      "    x = tmp + 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

// Alt 2: a local_parameter_declaration block item. The localparam's constant
// value is read back out of the block into the observed signal.
TEST(BlockItemDeclSim, LocalparamBlockItemProducesRuntimeValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    localparam int W = 8;\n"
      "    x = W;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 8u}});
}

// Alt 3: a parameter_declaration block item. Distinct alternative from the
// localparam form; its value likewise flows into the observed signal.
TEST(BlockItemDeclSim, ParameterBlockItemProducesRuntimeValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    parameter int D = 4;\n"
      "    x = D;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 4u}});
}

}  // namespace
