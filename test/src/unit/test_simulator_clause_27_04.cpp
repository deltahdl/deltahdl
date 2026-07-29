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

}  // namespace
