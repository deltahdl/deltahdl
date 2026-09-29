#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(CaseStatementSynth, AlwaysCombCaseStmt) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [1:0] sel, output logic [1:0] y);\n"
                   "  always_comb begin\n"
                   "    case (sel)\n"
                   "      2'b00: y = 2'b01;\n"
                   "      2'b01: y = 2'b10;\n"
                   "      default: y = 2'b00;\n"
                   "    endcase\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 2);
}

// §12.5 compares every bit of the case expression and the case items, once all
// of them are made as long as the longest. A shift is as long as its left
// operand (§11.6.1 Table 11-21), so `a << 1` is four bits long and matches
// 4'd6 only where its low four bits are 0110. The test fails on a lowering that
// compares bit 0 alone, which matches every even shift.
TEST(CaseStatementSynth, ASelectorThatIsNotANameIsComparedOverItsWidth) {
  ExpectInputSweep(
      "module m(input logic [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    case (a << 1)\n"
      "      4'd6: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a == 3 || a == 11 ? 1 : 0; });
}

// §12.5 makes the four-bit `a` five bits long beside the item 5'd16, which it
// never equals. The test fails on a lowering that compares over the
// selector's width alone, where the item's low four bits match `a` = 0.
TEST(CaseStatementSynth, AnItemWiderThanTheSelectorIsComparedOverItsWidth) {
  ExpectInputSweep(
      "module m(input logic [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    case (a)\n"
      "      5'd16: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t) -> uint64_t { return 0; });
}

// §11.8.2 carries the case's common length into the context-determined left
// operand of a shift, so `a << 1` keeps the bit it moves out of the top of `a`
// and reaches 16 at `a` = 8. The test fails on a lowering that sizes the shift
// by the selector alone, which drops that bit and never matches.
TEST(CaseStatementSynth, TheCommonLengthIsCarriedIntoTheSelector) {
  ExpectInputSweep(
      "module m(input logic [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    case (a << 1)\n"
      "      5'd16: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a == 8 ? 1 : 0; });
}

// §12.5 makes the comparison signed only where the case expression and every
// item are signed, and §11.8.2 then extends the context-determined operand of
// `>>>` by its sign. The signed `a` of 4'b1110 and 4'b1111 is -2 and -1, which
// shift right to the five-bit -1 the item writes. The test fails on a lowering
// that leaves the comparison unsigned, where `a` is zero-extended and the
// shift never sets bit 4.
TEST(CaseStatementSynth, ASignedCaseExtendsTheSelectorBySign) {
  ExpectInputSweep(
      "module m(input logic signed [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    case (a >>> 1)\n"
      "      5'sb11111: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a >= 14 ? 1 : 0; });
}

// One unsigned item makes the whole comparison unsigned (§12.5), so the same
// `a >>> 1` is zero-extended and never reaches 5'b11111.
TEST(CaseStatementSynth, AnUnsignedItemMakesTheComparisonUnsigned) {
  ExpectInputSweep(
      "module m(input logic signed [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    case (a >>> 1)\n"
      "      5'b11111: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t) -> uint64_t { return 0; });
}

// A case expression whose length the synthesizer cannot answer is one it
// cannot compare bit for bit. `SynthLower::ExprWidth` reads no function's
// declaration, so a call is such a selector.
TEST(CaseStatementSynth, ASelectorOfUnknownWidthIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic y);\n"
                   "  function logic [3:0] g(input logic [3:0] v); return v; "
                   "endfunction\n"
                   "  always_comb begin\n"
                   "    case (g(a))\n"
                   "      4'd6: y = 1'b1;\n"
                   "      default: y = 1'b0;\n"
                   "    endcase\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "case expression has no width in the synthesizer",
                            4, "12.5"));
}

}  // namespace
