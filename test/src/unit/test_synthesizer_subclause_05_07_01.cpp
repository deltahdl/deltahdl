#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(IntegerLiteralSynthesis, UnsizedDecimalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, result;\n"
                           "  assign result = 42;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedHexSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'hFF;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedBinarySynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [3:0] result;\n"
                           "  assign result = 4'b1010;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedOctalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'o77;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedDecimalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'd200;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnbasedUnsizedOneSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = '1;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnbasedUnsizedZeroSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = '0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnderscoreSeparatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] result;\n"
                           "  assign result = 32'hDEAD_BEEF;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SignedLiteralSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'sd99;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis,
     SizedLiteralZeroFillsBitSixtyFourOfAContinuousAssignTarget) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [127:0] y);\n"
                           "  assign y = 128'd5;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[64], AigGraph::kConstFalse);
}

TEST(IntegerLiteralSynthesis,
     SizedLiteralZeroFillsBitSixtyFourOfAProceduralTarget) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [127:0] y);\n"
                           "  always_comb y = 128'd5;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[64], AigGraph::kConstFalse);
}

TEST(IntegerLiteralSynthesis, WideDecimalLiteralWritesBitEighty) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [80:0] y);\n"
                           "  assign y = 81'd1208925819614629174706177;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 81u);
  EXPECT_EQ(aig->outputs[80], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[40], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

TEST(IntegerLiteralSynthesis, UnsizedWideDecimalLiteralWritesBitSeventy) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [71:0] y);\n"
                           "  assign y = 1180591620717411303424;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 72u);
  EXPECT_EQ(aig->outputs[70], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[69], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
}

static const AigGraph* LowerSrc(SynthFixture& f, const std::string& src) {
  const auto* mod = ElaborateSrc(f, src);
  if (mod == nullptr) return nullptr;
  SynthLower synth(f.arena, f.diag);
  return synth.Lower(mod);
}

TEST(IntegerLiteralSynthesis, SizedHexLiteralIsTruncatedFromTheLeftToItsSize) {
  SynthFixture f;
  const auto* aig = LowerSrc(f,
                             "module m(output logic [11:0] y);\n"
                             "  assign y = 8'hFFF;\n"
                             "endmodule\n");
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(EvalAigOutputs(*aig, 0), 0x0FFu);
}

TEST(IntegerLiteralSynthesis,
     SizedDecimalLiteralIsTruncatedFromTheLeftToItsSize) {
  SynthFixture f;
  const auto* aig = LowerSrc(f,
                             "module m(output logic [11:0] y);\n"
                             "  assign y = 8'd300;\n"
                             "endmodule\n");
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(EvalAigOutputs(*aig, 0), 44u);
}

TEST(IntegerLiteralSynthesis, WideDecimalLiteralDropsBitAtItsSize) {
  SynthFixture f;
  const auto* aig = LowerSrc(f,
                             "module m(output logic [95:0] y);\n"
                             "  assign y = 80'd1208925819614629174706177;\n"
                             "endmodule\n");
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 96u);
  EXPECT_EQ(aig->outputs[80], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

TEST(IntegerLiteralSynthesis, CasezPatternDigitAboveItsSizeIsTruncated) {
  ExpectInputSweep(
      "module m(input [7:0] sel, output logic y);\n"
      "  always_comb begin\n"
      "    casez (sel)\n"
      "      4'b?0000: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      32, [](uint64_t sel) { return sel == 0 ? uint64_t{1} : uint64_t{0}; });
}

static std::string CaseItemSrc(const char* kind, int width, const char* item) {
  return std::string("module m(input [") + std::to_string(width - 1) +
         ":0] sel, output logic y);\n"
         "  always_comb begin\n"
         "    " +
         kind + " (sel)\n      " + item +
         ": y = 1'b1;\n"
         "      default: y = 1'b0;\n"
         "    endcase\n"
         "  end\n"
         "endmodule\n";
}

TEST(IntegerLiteralSynthesis, CasezDontCareDigitPadsTheWholeSizedPattern) {
  ExpectInputSweep(CaseItemSrc("casez", 8, "8'b?"), 256,
                   [](uint64_t) { return uint64_t{1}; });
}

TEST(IntegerLiteralSynthesis, CasezLeftmostDontCareDigitPadsAboveTheDigits) {
  ExpectInputSweep(CaseItemSrc("casez", 8, "8'b?1"), 256,
                   [](uint64_t sel) { return sel & 1u; });
}

TEST(IntegerLiteralSynthesis, CasexLeftmostXDigitPadsAboveTheDigits) {
  ExpectInputSweep(CaseItemSrc("casex", 8, "8'bx1"), 256,
                   [](uint64_t sel) { return sel & 1u; });
}

TEST(IntegerLiteralSynthesis, CasezLeftmostOctalDontCareDigitPadsAboveItself) {
  ExpectInputSweep(CaseItemSrc("casez", 8, "8'o?1"), 256, [](uint64_t sel) {
    return (sel & 7u) == 1 ? uint64_t{1} : uint64_t{0};
  });
}

TEST(IntegerLiteralSynthesis, CasexLeftmostHexXDigitPadsAboveItsFourBits) {
  ExpectInputSweep(CaseItemSrc("casex", 12, "12'hx1"), 4096, [](uint64_t sel) {
    return (sel & 15u) == 1 ? uint64_t{1} : uint64_t{0};
  });
}

TEST(IntegerLiteralSynthesis,
     CasezUnsizedDontCarePatternIsExtendedToTheSelectorWidth) {
  SynthFixture f;
  const auto* aig = LowerSrc(f, CaseItemSrc("casez", 40, "'b?1"));
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const uint64_t kBitThirtySix = uint64_t{1} << 36;
  EXPECT_EQ(EvalAigOutputs(*aig, 1), 1u);
  EXPECT_EQ(EvalAigOutputs(*aig, 5), 1u);
  EXPECT_EQ(EvalAigOutputs(*aig, kBitThirtySix | 1u), 1u);
  EXPECT_EQ(EvalAigOutputs(*aig, 2), 0u);
  EXPECT_EQ(EvalAigOutputs(*aig, kBitThirtySix), 0u);
}

}  // namespace
