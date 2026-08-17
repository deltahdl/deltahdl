#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §27.4: "Within the generate block of a loop generate construct, there is an
// implicit localparam declaration. This is an integer parameter that has the
// same name and type as the loop index, and its value within each instance of
// the generate block is the value of the loop index at the time the instance
// was elaborated." The genvar itself "does not exist at simulation time", so a
// reference to the name inside the block is a reference to that localparam.
//
// Every instance runs one shared body, so the value has to be private to the
// instance. Delaying each instance by a different amount interleaves the four
// bodies and makes the assignments run in the reverse of elaboration order: a
// value shared between the instances would leave every element holding the
// index of whichever instance ran last, rather than its own.
TEST(LoopGenerateIndexSim, IndexHoldsItsOwnInstanceValueAcrossADelay) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      initial begin\n"
                 "        #(4 - i);\n"
                 "        out[i] = i + 8'd10;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {10u, 11u, 12u, 13u});
}

// §27.4: each loop generate construct contributes its own implicit localparam,
// and a generate block nested in two of them is one instance of each. Both loop
// indices are therefore in scope in the innermost body, holding the values that
// selected this instance.
TEST(LoopGenerateIndexSim, NestedBlockSeesBothEnclosingIndices) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
                 "      for (genvar j = 0; j < 2; j = j + 1) begin : h\n"
                 "        initial out[i * 2 + j] = i * 8'd10 + j;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {0u, 1u, 10u, 11u});
}

// §27.4: the implicit localparam "can be used anywhere within the generate
// block that a normal parameter with an integer value can be used", which
// includes a continuous assignment. Each instance's assignment drives the
// element its own index selects, from a right-hand side its own index scales.
TEST(LoopGenerateIndexSim, ContinuousAssignmentSeesItsInstanceIndex) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      assign out[i] = i * 8'd3;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {0u, 3u, 6u, 9u});
}

// §27.4: the loop index is an integer, so the parameter named after it is
// signed. A descending loop that runs the index negative therefore compares as
// negative, rather than wrapping to a large unsigned value.
TEST(LoopGenerateIndexSim, NegativeIndexIsSigned) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:2];\n"
                 "  generate\n"
                 "    for (genvar i = -1; i < 2; i = i + 1) begin : g\n"
                 "      initial out[i + 1] = (i < 0) ? 8'd7 : 8'd9;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {7u, 9u, 9u});
}

// §27.4: a generate block "comprises a separate scope and a new level of
// hierarchy when it is instantiated", so a declaration inside the block belongs
// to the instance and is named by its simple name from within it. Each instance
// stores a different value in its own `x` and reads it back, so an instance
// finding nothing (or finding a neighbour's) shows up as the wrong element.
TEST(LoopGenerateIndexSim, BlockLocalDeclarationIsReadBackWithinItsInstance) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = i + 8'd20;\n"
                 "        out[i] = x;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {20u, 21u, 22u, 23u});
}

// §27.4: the block's scope is the inner one, so a declaration in it hides a
// like-named declaration of the enclosing module for references written inside
// the block. The module-level `v` keeps the value its own process gave it,
// which distinguishes hiding from the instances writing through to it.
TEST(LoopGenerateIndexSim, BlockLocalDeclarationHidesTheModuleLevelName) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:1];\n"
                 "  logic [7:0] v;\n"
                 "  initial v = 8'd99;\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
                 "      logic [7:0] v;\n"
                 "      initial begin\n"
                 "        v = i + 8'd5;\n"
                 "        out[i] = v;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {5u, 6u});
  auto* outer = f.ctx.FindVariable("v");
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->value.ToUint64(), 99u);
}

// §27.4: a named generate block "is a declaration of an array of generate
// block instances", and "the index values in this array are the values assumed
// by the genvar during elaboration". Two sibling blocks written over one genvar
// are therefore two distinct arrays, and since each instance "comprises a
// separate scope and a new level of hierarchy when it is instantiated", `a`'s
// `x` at index 4 and `b`'s `x` at index 4 are different objects.
//
// Every instance writes its block's constant before any instance reads one
// back, so a run that gave the two blocks one object leaves both reads holding
// whichever write ran last, rather than each block's own constant. The loop
// runs 4 to 5 while the array it reports through is read at 0 to 3, so no index
// equals the offset of the element it selects.
TEST(LoopGenerateIndexSim, SiblingBlocksOverOneGenvarKeepSeparateVariables) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  genvar i;\n"
                 "  generate\n"
                 "    for (i = 4; i < 6; i = i + 1) begin : a\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = 8'd10;\n"
                 "        #1 out[i - 4] = x;\n"
                 "      end\n"
                 "    end\n"
                 "    for (i = 4; i < 6; i = i + 1) begin : b\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = 8'd20;\n"
                 "        #1 out[i - 2] = x;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {10u, 10u, 20u, 20u});
}

}  // namespace
