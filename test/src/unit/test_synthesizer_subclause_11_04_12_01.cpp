#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ReplicationSynthesis, ReplicationJoinsThatManyCopiesOfItsOperand) {
  ExpectInputSweep(
      "module m(input [1:0] a, output logic [5:0] y);\n"
      "  assign y = {3{a}};\n"
      "endmodule\n",
      4, [](uint64_t a) { return a | (a << 2) | (a << 4); });
}

TEST(ReplicationSynthesis, ReplicationInsideAConcatenationTakesItsOwnOffset) {
  ExpectInputSweep(
      "module m(input [1:0] a, input [2:0] b, output logic [6:0] y);\n"
      "  assign y = {b, {2{a}}};\n"
      "endmodule\n",
      32, [](uint64_t v) {
        uint64_t a = v & 0x3u;
        uint64_t b = (v >> 2) & 0x7u;
        return (b << 4) | (a << 2) | a;
      });
}

TEST(ReplicationSynthesis, AnOperandOfUnknownWidthIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [7:0] y);\n"
                   "  function logic [3:0] g(input logic [3:0] v); return v; "
                   "endfunction\n"
                   "  assign y = {2{g(a)}};\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "replication has no lowering",
                            3, "11.4.12.1"));
}

}  // namespace
