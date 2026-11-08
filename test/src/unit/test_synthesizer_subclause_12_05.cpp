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

TEST(CaseStatementSynth, ASignedNameSelectorIsExtendedBySign) {
  ExpectInputSweep(
      "module m(input logic signed [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    case (a)\n"
      "      5'sb11111: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a == 15 ? 1 : 0; });
}

TEST(CaseStatementSynth, AnUnsignedItemZeroExtendsASignedNameSelector) {
  ExpectInputSweep(
      "module m(input logic signed [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    case (a)\n"
      "      5'b11111: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t) -> uint64_t { return 0; });
}

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
