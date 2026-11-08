#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(VectorSelect, BitSelectResolvesTheIndexAgainstTheDeclaredRange) {
  ExpectInputSweep(
      "module m(input [8:1] data, output y);\n"
      "  assign y = data[3];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 2) & 1u; });
}

TEST(VectorSelect, BitSelectOfAnAscendingVectorReachesTheOppositeEnd) {
  ExpectInputSweep(
      "module m(input [1:8] data, output y);\n"
      "  assign y = data[3];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 5) & 1u; });
}

TEST(VectorSelect, NonIndexedPartSelectCarriesTheAddressedBits) {
  ExpectInputSweep(
      "module m(input [8:1] data, output [3:0] y);\n"
      "  assign y = data[8:5];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 4) & 0xFu; });
}

TEST(VectorSelect, IndexedPartSelectPlusAscendsFromItsBase) {
  ExpectInputSweep(
      "module m(input [8:1] data, output [3:0] y);\n"
      "  assign y = data[2+:4];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 1) & 0xFu; });
}

TEST(VectorSelect, IndexedPartSelectMinusDescendsFromItsBase) {
  ExpectInputSweep(
      "module m(input [8:1] data, output [3:0] y);\n"
      "  assign y = data[8-:4];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 4) & 0xFu; });
}

TEST(VectorSelect, SelectOfAnInternalNetResolvesAgainstItsDeclaration) {
  ExpectInputSweep(
      "module m(input [7:0] a, output y);\n"
      "  wire [8:1] w;\n"
      "  assign w = a;\n"
      "  assign y = w[3];\n"
      "endmodule\n",
      256, [](uint64_t a) { return (a >> 2) & 1u; });
}

TEST(VectorSelect, ContinuousAssignToAPartSelectWritesOnlyThoseBits) {
  ExpectInputSweep(
      "module m(input [3:0] a, output [8:1] y);\n"
      "  assign y[8:5] = a;\n"
      "  assign y[4:1] = ~a;\n"
      "endmodule\n",
      16, [](uint64_t a) { return ((a & 0xFu) << 4) | (~a & 0xFu); });
}

TEST(VectorSelect, ProceduralAssignToABitSelectWritesOnlyThatBit) {
  ExpectInputSweep(
      "module m(input a, output logic [8:1] y);\n"
      "  always_comb begin\n"
      "    y = 8'b0;\n"
      "    y[3] = a;\n"
      "  end\n"
      "endmodule\n",
      2, [](uint64_t a) { return a != 0 ? uint64_t{4} : uint64_t{0}; });
}

TEST(VectorSelect, ConcatenationLvalueSplitLowersItsPartSelects) {
  ExpectInputSweep(
      "module m(input [7:0] word, output [3:0] hi, output [3:0] lo);\n"
      "  assign {hi, lo} = word;\n"
      "endmodule\n",
      256, [](uint64_t word) {
        return ((word >> 4) & 0xFu) | ((word & 0xFu) << 4);
      });
}

TEST(VectorSelect, BitSelectByAVariableIndexChoosesAmongTheBits) {
  ExpectInputSweep(
      "module m(input [8:1] data, input [1:0] s, output y);\n"
      "  assign y = data[s + 5];\n"
      "endmodule\n",
      1024, [](uint64_t v) {
        uint64_t data = v & 0xFFu;
        uint64_t s = (v >> 8) & 0x3u;
        return (data >> (4 + s)) & 1u;
      });
}

TEST(VectorSelect, IndexedPartSelectByAVariableBaseAscendsFromIt) {
  ExpectInputSweep(
      "module m(input [8:1] data, input [1:0] s, output [1:0] y);\n"
      "  assign y = data[s + 3 +: 2];\n"
      "endmodule\n",
      1024, [](uint64_t v) {
        uint64_t data = v & 0xFFu;
        uint64_t s = (v >> 8) & 0x3u;
        return (data >> (s + 2)) & 0x3u;
      });
}

TEST(VectorSelect,
     AssignToABitSelectByAVariableIndexIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [8:1] data, input [1:0] s, output logic "
                   "[8:1] y);\n"
                   "  always_comb begin\n"
                   "    y = 8'b0;\n"
                   "    y[s] = data[1];\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment target has no lowering", 4, ""));
}

TEST(VectorSelect, SelectOverAnArithmeticExpressionCarriesItsBits) {
  ExpectInputSweep(
      "module m(input [3:0] ina, input [3:0] inb, input carry_in,\n"
      "         output carry_out, output [3:0] sum_out);\n"
      "  assign {carry_out, sum_out} = ina + inb + carry_in;\n"
      "endmodule\n",
      512, [](uint64_t v) {
        uint64_t sum = (v & 0xFu) + ((v >> 4) & 0xFu) + ((v >> 8) & 0x1u);
        return ((sum >> 4) & 0x1u) | ((sum & 0xFu) << 1);
      });
}

TEST(VectorSelect, SelectOverAConcatenationCrossesItsOperands) {
  ExpectInputSweep(
      "module m(input [1:0] a, input [1:0] b, output [1:0] y);\n"
      "  assign y = {a, b}[2:1];\n"
      "endmodule\n",
      16, [](uint64_t v) { return ((v & 0x1u) << 1) | ((v >> 3) & 0x1u); });
}

}  // namespace
