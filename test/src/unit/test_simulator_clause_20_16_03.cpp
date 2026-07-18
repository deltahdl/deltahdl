#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Writes `data` to a scratch file tagged by `tag` and returns its path. The
// path holds no characters that need escaping inside a SystemVerilog string
// literal, so it embeds directly in the source under test.
std::string WritePersonalityFile(const std::string& tag,
                                 const std::string& data) {
  std::string path = "/tmp/deltahdl_t201603_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

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

// §20.16.3: the personality "is normally loaded into the memory from a text
// data file using the system tasks $readmemb or $readmemh (see 21.4)." This is
// the primary loading form the subclause names; the procedural-assignment tests
// above cover only the stated alternative. Build the personality memory from
// §21.4's real $readmemb syntax and confirm the loaded contents drive the PLA
// outputs. With the mem declared two input terms wide and two output terms
// deep, ascending, $readmemb fills mem[1]=2'b10 and mem[2]=2'b01; under
// $sync$and$array with in = 2'b10 the high input reaches the MSB output and the
// low input reaches the LSB output, so out == 2'b10.
TEST(PlaPersonality, LoadedByReadmemb) {
  SimFixture f;
  std::string path = WritePersonalityFile("readmemb", "10\n01\n");
  std::string src =
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:2];\n"
      "  logic [1:2] out;\n"
      "  initial begin\n"
      "    in = 2'b10;\n"
      "    $readmemb(\"" +
      path +
      "\", mem);\n"
      "    $sync$and$array(mem, in, out);\n"
      "  end\n"
      "endmodule\n";
  uint64_t out = RunModule(f, src.c_str(), "out");
  std::remove(path.c_str());
  EXPECT_EQ(out, 2u);
}

// §20.16.3 names both $readmemb and $readmemh (see 21.4) as the tasks that load
// a personality from a file; $readmemh parses each word as hexadecimal, a
// different §21.4 code path from the binary form above. Build the personality
// from §21.4's real $readmemh syntax and confirm the loaded contents drive a
// $sync$or$array reduction. mem[1]=2'b01 and mem[2]=2'b10 (hex 1 then 2); with
// in = 2'b10 the OR selects nothing for the MSB output and the high input for
// the LSB output, so out == 2'b01.
TEST(PlaPersonality, LoadedByReadmemh) {
  SimFixture f;
  std::string path = WritePersonalityFile("readmemh", "1\n2\n");
  std::string src =
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:2];\n"
      "  logic [1:2] out;\n"
      "  initial begin\n"
      "    in = 2'b10;\n"
      "    $readmemh(\"" +
      path +
      "\", mem);\n"
      "    $sync$or$array(mem, in, out);\n"
      "  end\n"
      "endmodule\n";
  uint64_t out = RunModule(f, src.c_str(), "out");
  std::remove(path.c_str());
  EXPECT_EQ(out, 1u);
}

}  // namespace
