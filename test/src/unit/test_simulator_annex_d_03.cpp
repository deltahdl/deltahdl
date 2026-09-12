#include <string>

#include "fixture_simulator.h"

// Annex D.3: $getpattern "provides for fast processing of stimulus patterns
// that have to be propagated to a large number of scalar inputs", reading a
// pattern from a memory element and driving it, through the continuous
// assignment it stands in, onto the concatenation of scalar nets. D.3's
// example steps an index through the memory and has "a new pattern ... applied
// to the circuit each time index changes value". The function was parsed and
// evaluated by nothing, so the nets took a zero for every pattern.

using namespace delta;

namespace {

// D.3's example reduced to three inputs and two patterns loaded by
// assignment: each change of the index drives the word it names onto the
// nets, the leftmost net taking the word's first bit.
TEST(GetpatternSim, EachIndexChangeDrivesThePatternItNames) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  integer index;\n"
      "  wire i1, i2, i3;\n"
      "  assign {i1, i2, i3} = $getpattern(in_mem[index]);\n"
      "  initial begin\n"
      "    in_mem[1] = 3'b101;\n"
      "    in_mem[2] = 3'b010;\n"
      "    index = 1;\n"
      "    #1 $display(\"%b%b%b\", i1, i2, i3);\n"
      "    index = 2;\n"
      "    #1 $display(\"%b%b%b\", i1, i2, i3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "101\n010\n");
}

}  // namespace
