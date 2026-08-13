#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ImplicitEventSynthesis, AlwaysStarCombLogic) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output logic y);\n"
                           "  always @* y = a & b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

TEST(ImplicitEventSynthesis, AlwaysStarIfElseNoLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input sel, input a, input b,\n"
                           "         output logic y);\n"
                           "  always @* begin\n"
                           "    if (sel) y = a;\n"
                           "    else     y = b;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

TEST(ImplicitEventSynthesis, AlwaysStarCaseNoLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [1:0] sel,\n"
                           "         output logic [7:0] y);\n"
                           "  always @* begin\n"
                           "    case (sel)\n"
                           "      2'b00: y = 8'h10;\n"
                           "      2'b01: y = 8'h20;\n"
                           "      2'b10: y = 8'h30;\n"
                           "      default: y = 8'hFF;\n"
                           "    endcase\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

// The sweep fails on a netlist whose `sum` is not `a + b` or whose `diff` is
// not `a - b`. The three assertions above it are what §9.4.2.2 makes this case
// about, that an `always @(*)` block writing two outputs lowers to
// combinational logic, and all three hold over a netlist in which every bit of
// both outputs is a constant zero: such a graph is non-null, has outputs, and
// has no latches. That is the netlist a `SynthLower::LowerBinaryBit` with no
// arm for `+` builds, so the sweep is what states that the two statements
// computed anything.
//
// `SynthLower::MapPorts` allocates an input for each bit of each input port in
// declaration order, least significant bit first, and
// `SynthLower::RegisterOutputs` registers the output ports the same way, so
// input bit i carries `a[i]`, input bit i + 4 carries `b[i]`, output bit i
// carries `sum[i]` and output bit i + 4 carries `diff[i]`.
//
// The ports are four bits wide so that all 256 pairs can be driven rather than
// the 65536 pairs eight-bit ports would take. Four bits is a carry chain long
// enough that a netlist propagating no carry disagrees, and it holds the wrap
// at both ends: `4'hF + 4'h1` carries out of the top, and `4'h0 - 4'h1` leaves
// `4'hF`.
TEST(ImplicitEventSynthesis, AlwaysStarMultipleOutputs) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, input [3:0] b,\n"
                           "         output logic [3:0] sum,\n"
                           "         output logic [3:0] diff);\n"
                           "  always @(*) begin\n"
                           "    sum = a + b;\n"
                           "    diff = a - b;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
  for (uint64_t a = 0; a < 16; ++a) {
    for (uint64_t b = 0; b < 16; ++b) {
      uint64_t expected = ((a + b) & 0xFU) | (((a - b) & 0xFU) << 4);
      EXPECT_EQ(EvalAigOutputs(*aig, a | (b << 4)), expected)
          << "a = " << a << ", b = " << b;
    }
  }
}

}  // namespace
