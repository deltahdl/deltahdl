#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.16.3 covers the logic array personality: its declaration, its loading,
// and the requirement that a dynamically changed personality "shall be
// reflected on the outputs of the logic array at the next evaluation." The
// ascending-order rule is checked at the elaborator stage
// (test_elaborator_clause_20_16_03). The behaviors observed here are
// simulation-stage: the personality may be written directly into the memory
// with procedural assignments (the alternative to the §21.4 $readmem loading),
// and a change to the personality memory takes effect at the next evaluation of
// the array. What counts as an "evaluation" is the array-type behavior defined
// by §20.16.1; these tests exercise that shared PLA evaluation engine through
// the personality memory.

// §20.16.3: the personality can be written directly into the memory with
// procedural assignment statements rather than loaded from a file. A memory
// declared as wide as the input terms and as deep as the output terms, filled
// this way, drives each output from its own personality word.
TEST(PlaPersonality, LoadedByProceduralAssignment) {
  SimFixture f;
  // Two output terms (depth 2), two input terms (width 2). With in = 2'b10,
  // word mem[1] selects the high input for the MSB output and mem[2] selects
  // the low input for the LSB output, so out == 2'b10.
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:2];\n"
                           "  logic [1:2] out;\n"
                           "  initial begin\n"
                           "    in = 2'b10;\n"
                           "    mem[1] = 2'b10;\n"
                           "    mem[2] = 2'b01;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 2u);
}

// §20.16.3: "The new personality shall be reflected on the outputs of the logic
// array at the next evaluation." A synchronous array's next evaluation is its
// next call; changing the personality memory between two calls makes the second
// call reflect the new personality.
TEST(PlaPersonality, ChangeReflectedAtNextEvaluation) {
  SimFixture f;
  // in = 2'b10 throughout. The first personality selects both inputs, so the
  // AND is 0; the dynamically rewritten personality selects only the high
  // input, so the next evaluation yields 1.
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] first;\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    in = 2'b10;\n"
                           "    mem[1] = 2'b11;\n"
                           "    $sync$and$array(mem, in, first);\n"
                           "    mem[1] = 2'b10;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

// §20.16.3: the same dynamic change, with a synchronous array, must NOT affect
// the outputs until that next evaluation. The output captured from the first
// call still reflects the original personality even though the memory was
// rewritten afterward.
TEST(PlaPersonality, ChangeNotReflectedBeforeNextEvaluation) {
  SimFixture f;
  uint64_t first = RunModule(f,
                             "module t;\n"
                             "  logic [1:2] in;\n"
                             "  logic [1:2] mem [1:1];\n"
                             "  logic [1:1] first;\n"
                             "  logic [1:1] out;\n"
                             "  initial begin\n"
                             "    in = 2'b10;\n"
                             "    mem[1] = 2'b11;\n"
                             "    $sync$and$array(mem, in, first);\n"
                             "    mem[1] = 2'b10;\n"
                             "    $sync$and$array(mem, in, out);\n"
                             "  end\n"
                             "endmodule\n",
                             "first");
  EXPECT_EQ(first, 0u);
}

}  // namespace
