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
// PLA engine (eval_systask_pla.cpp) carries this rule: ClassifyPlaTask decodes
// the logic component of the task name and PlaReduceWord reduces each
// personality word with the corresponding function - an AND reduction for
// and/nand and an OR reduction for or/nor, with the result complemented for
// the nand/nor forms.
// These tests drive small arrays so that each of the four logic functions is
// observable from the output term, and exercise the nor/nand planes in the
// plane format and the asynchronous type to confirm the functions apply across
// types and formats.

// §20.16.2: all four logic planes are modeled, and the second sentence makes
// the set of logic functions orthogonal to the other two task-name
// components: every logic plane is available under
// both array types (§20.16.1 sync/async) and both personality formats
// (§20.16.4 array/plane). This sweep drives the identical personality word and
// inputs through all sixteen task names of Table 20-12. Personality code 1
// takes the true input value in both formats, so every type/format cell is
// expected to reduce the same participating inputs and each column reads its
// logic function's value: and 0, or 1, nand 1, nor 0. A logic function missing
// from any type/format cell, or a cell that let the type or format leak into
// the chosen function, would break its column's expected value.
TEST(PlaArrayLogicType, LogicPlanesApplyAcrossAllTypesAndFormats) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] saa, soa, snda, snra;\n"
      "  logic [1:1] aaa, aoa, anda, anra;\n"
      "  logic [1:1] sap, sop, sndp, snrp;\n"
      "  logic [1:1] aap, aop, andp, anrp;\n"
      "  initial begin\n"
      "    mem[1] = 2'b11;\n"  // both formats: take both true inputs
      "    in = 2'b10;\n"
      "    $sync$and$array(mem, in, saa);\n"
      "    $sync$or$array(mem, in, soa);\n"
      "    $sync$nand$array(mem, in, snda);\n"
      "    $sync$nor$array(mem, in, snra);\n"
      "    $async$and$array(mem, in, aaa);\n"
      "    $async$or$array(mem, in, aoa);\n"
      "    $async$nand$array(mem, in, anda);\n"
      "    $async$nor$array(mem, in, anra);\n"
      "    $sync$and$plane(mem, in, sap);\n"
      "    $sync$or$plane(mem, in, sop);\n"
      "    $sync$nand$plane(mem, in, sndp);\n"
      "    $sync$nor$plane(mem, in, snrp);\n"
      "    $async$and$plane(mem, in, aap);\n"
      "    $async$or$plane(mem, in, aop);\n"
      "    $async$nand$plane(mem, in, andp);\n"
      "    $async$nor$plane(mem, in, anrp);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  // Each type/format cell reads and=0, or=1, nand=1, nor=0 on input 10.
  const char* and_outs[] = {"saa", "aaa", "sap", "aap"};
  const char* or_outs[] = {"soa", "aoa", "sop", "aop"};
  const char* nand_outs[] = {"snda", "anda", "sndp", "andp"};
  const char* nor_outs[] = {"snra", "anra", "snrp", "anrp"};
  for (const char* name : and_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 0u) << name;  // and:  1 & 0
  }
  for (const char* name : or_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 1u) << name;  // or:   1 | 0
  }
  for (const char* name : nand_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 1u) << name;  // nand: ~(1 & 0)
  }
  for (const char* name : nor_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 0u) << name;  // nor:  ~(1 | 0)
  }
}

// §20.16.2 applies the four logic functions to all formats, including the plane
// format of §20.16.4. This is the $sync$nand$plane task form of the subclause's
// second example. With both personality codes 0 (take the complemented input)
// and both inputs high, each term is ~1 = 0, the and reduction is 0, and the
// nand complement drives the output high. The array format instead takes
// neither input (leaving the and identity 1) and reads 0, so the plane result
// is specific to the nand function reducing in the plane format - the test
// drives the same personality through $sync$nand$array to observe the
// contrast, so a format-agnostic reduction could not satisfy both outputs.
TEST(PlaArrayLogicType, NandPlaneAppliesNandInPlaneFormat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] out_plane, out_array;\n"
      "  initial begin\n"
      "    mem[1] = 2'b00;\n"  // plane codes: take complemented inputs
      "    in = 2'b11;\n"
      "    $sync$nand$plane(mem, in, out_plane);\n"
      "    $sync$nand$array(mem, in, out_array);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* out_plane = f.ctx.FindVariable("out_plane");
  auto* out_array = f.ctx.FindVariable("out_array");
  ASSERT_NE(out_plane, nullptr);
  ASSERT_NE(out_array, nullptr);
  EXPECT_EQ(out_plane->value.ToUint64(), 1u);  // nand of (~1, ~1) = ~(0 & 0)
  EXPECT_EQ(out_array->value.ToUint64(), 0u);  // no inputs taken: ~(identity 1)
}

// §20.16.2's example calls consume input and output terms written as
// concatenations of scalar signals (the term forms of §20.16's syntax), and a
// logic array with several personality words applies its logic function once
// per word. Here a two-word nand array reduces concatenated scalar inputs:
// word 1 takes both inputs (nand of 1,0 = 1) and word 2 takes only the first
// (nand of 1 = 0), so the concatenated outputs read b1=1, b2=0. An and
// reduction over the same personality would read the inverse pair (0,1), so
// the per-word application of the named function is what these values observe.
TEST(PlaArrayLogicType, LogicFunctionAppliesPerWordOverConcatenatedTerms) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a1, a2;\n"
      "  logic b1, b2;\n"
      "  logic [1:2] mem [1:2];\n"
      "  initial begin\n"
      "    mem[1] = 2'b11;\n"  // word 1: take both inputs
      "    mem[2] = 2'b10;\n"  // word 2: take a1 only
      "    a1 = 1; a2 = 0;\n"
      "    $sync$nand$array(mem, {a1,a2}, {b1,b2});\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b1 = f.ctx.FindVariable("b1");
  auto* b2 = f.ctx.FindVariable("b2");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b1->value.ToUint64(), 1u);  // nand: ~(1 & 0)
  EXPECT_EQ(b2->value.ToUint64(), 0u);  // nand: ~(1)
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
