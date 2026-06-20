#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.16.2 states that PLA logic arrays are modeled with four logic planes -
// and, or, nand, and nor - and that this set of logic functions applies to all
// array types (the synchronous/asynchronous forms of §20.16.1) and all
// personality formats (the array/plane formats of §20.16.4). The simulator's
// PLA engine (eval_systask.cpp) carries this rule: ClassifyPlaTask decodes the
// logic component of the task name and PlaReduceWord reduces each personality
// word with the corresponding function - an AND reduction for and/nand and an
// OR reduction for or/nor, with the result complemented for the nand/nor forms.
// These tests drive small arrays so that each of the four logic functions is
// observable from the output term, and exercise the nor/nand planes in the
// plane format and the asynchronous type to confirm the functions apply across
// types and formats.

// §20.16.2: all four logic planes are modeled. Driving the identical
// personality memory (both inputs taken) and inputs (one high, one low) through
// and/or/nand/ nor arrays makes each function produce its own documented value:
// and -> 1&0=0, or -> 1|0=1, nand -> ~(1&0)=1, nor -> ~(1|0)=0. The four
// distinct results show that the logic component of the task name selects the
// modeled logic function.
TEST(PlaArrayLogicType, AllFourLogicPlanesProduceTheirFunctions) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] o_and, o_or, o_nand, o_nor;\n"
      "  initial begin\n"
      "    mem[1] = 2'b11;\n"  // take both inputs
      "    in = 2'b10;\n"      // one input high, one low
      "    $sync$and$array(mem, in, o_and);\n"
      "    $sync$or$array(mem, in, o_or);\n"
      "    $sync$nand$array(mem, in, o_nand);\n"
      "    $sync$nor$array(mem, in, o_nor);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* o_and = f.ctx.FindVariable("o_and");
  auto* o_or = f.ctx.FindVariable("o_or");
  auto* o_nand = f.ctx.FindVariable("o_nand");
  auto* o_nor = f.ctx.FindVariable("o_nor");
  ASSERT_NE(o_and, nullptr);
  ASSERT_NE(o_or, nullptr);
  ASSERT_NE(o_nand, nullptr);
  ASSERT_NE(o_nor, nullptr);
  EXPECT_EQ(o_and->value.ToUint64(), 0u);   // and:  1 & 0
  EXPECT_EQ(o_or->value.ToUint64(), 1u);    // or:   1 | 0
  EXPECT_EQ(o_nand->value.ToUint64(), 1u);  // nand: ~(1 & 0)
  EXPECT_EQ(o_nor->value.ToUint64(), 0u);   // nor:  ~(1 | 0)
}

// §20.16.2 applies the four logic functions to all formats, including the plane
// format of §20.16.4. This is the $sync$nand$plane task form of the subclause's
// second example. With both personality codes 0 (take the complemented input)
// and both inputs high, each term is ~1 = 0, the and reduction is 0, and the
// nand complement drives the output high. The array format would instead take
// neither input (leaving the and identity 1) and read 0, so this result is
// specific to the nand function reducing in the plane format.
TEST(PlaArrayLogicType, NandPlaneAppliesNandInPlaneFormat) {
  SimFixture f;
  uint64_t out = RunModule(
      f,
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] out;\n"
      "  initial begin\n"
      "    mem[1] = 2'b00;\n"  // plane codes: take complemented inputs
      "    in = 2'b11;\n"
      "    $sync$nand$plane(mem, in, out);\n"
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(out, 1u);  // nand of (~1, ~1) = ~(0 & 0)
}

// §20.16.2 applies the four logic functions to all array types, including the
// asynchronous form of §20.16.1, and to the plane format. This is the
// $async$nor$plane task form of the subclause's first example. Both personality
// codes are 0 (take the complemented input). Starting with both inputs low,
// each term is ~0 = 1, the or reduction is 1, and the nor complement reads 0.
// Raising both inputs makes the asynchronous array re-evaluate on its own: each
// term becomes ~1 = 0, the or reduction is 0, and the nor output rises to 1 -
// showing the nor function applied under the asynchronous type in the plane
// format.
TEST(PlaArrayLogicType, AsyncNorPlaneReevaluatesNorInPlaneFormat) {
  SimFixture f;
  uint64_t out = RunModule(
      f,
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] out;\n"
      "  initial begin\n"
      "    mem[1] = 2'b00;\n"  // plane codes: take complemented inputs
      "    in = 2'b00;\n"
      "    $async$nor$plane(mem, in, out);\n"  // ~(~0 | ~0) = 0
      "    #1 in = 2'b11;\n"                   // async re-eval: ~(~1 | ~1) = 1
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(out, 1u);
}

}  // namespace
