#include <gtest/gtest.h>

#include <array>
#include <cstdint>

#include "elaborator/rtlir.h"
#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(TypeOperatorSynthesis, FoldedComparisonLowersToTheBitItStandsFor) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f,
      "module m(input [3:0] a, input [3:0] b, output logic [2:0] y);\n"
      "  assign y = {type(a) == type(b), type(a) == type(bit [3:0]),\n"
      "              type(a + b) == type(logic [3:0])};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[2], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[1], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

TEST(TypeOperatorSynthesis, TypeReferenceIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(output logic y);\n"
                   "  logic [3:0] u [4];\n"
                   "  assign y = (type(u[0:1]) == type(u[2:3]));\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the type operator has no lowering", 3, "6.23"));
}

TEST(TypeOperatorSynthesis, EachInstanceLowersItsOwnComparison) {
  SynthFixture f;
  const auto* top = ElaborateSrc(
      f,
      "module w #(type T = int, int W = 8)(output logic [3:0] y);\n"
      "  T x;\n"
      "  logic [W-1:0] v;\n"
      "  assign y[3:2] = {type(x) == type(int), type(v) == type(logic "
      "[7:0])};\n"
      "  always_comb y[1:0] = {type(x) != type(int), type(v) !== type(logic "
      "[7:0])};\n"
      "endmodule\n"
      "module t; w #(int, 4) d(); w #(byte, 8) c(); endmodule\n");
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 2u);
  struct Expected {
    const char* inst;
    std::array<uint32_t, 4> bits;
  };
  for (const Expected& e :
       {Expected{"d",
                 {AigGraph::kConstTrue, AigGraph::kConstFalse,
                  AigGraph::kConstFalse, AigGraph::kConstTrue}},
        Expected{"c",
                 {AigGraph::kConstFalse, AigGraph::kConstTrue,
                  AigGraph::kConstTrue, AigGraph::kConstFalse}}}) {
    SCOPED_TRACE(e.inst);
    const RtlirModule* inst = nullptr;
    for (const auto& child : top->children) {
      if (child.inst_name == e.inst) inst = child.resolved;
    }
    ASSERT_NE(inst, nullptr);
    SynthLower synth(f.arena, f.diag);
    auto* aig = synth.Lower(inst);
    ASSERT_NE(aig, nullptr);
    ASSERT_EQ(aig->outputs.size(), 4u);
    EXPECT_EQ(aig->outputs[0], e.bits[0]);
    EXPECT_EQ(aig->outputs[1], e.bits[1]);
    EXPECT_EQ(aig->outputs[2], e.bits[2]);
    EXPECT_EQ(aig->outputs[3], e.bits[3]);
  }
}

TEST(TypeOperatorSynthesis, EachLoopIterationLowersItsOwnComparison) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(output logic [1:0] y);\n"
                   "  for (genvar i = 0; i < 2; i++) begin : g\n"
                   "    logic [i:0] v;\n"
                   "    assign y[i] = type(v) == type(logic [0:0]);\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 2u);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[1], AigGraph::kConstFalse);
}

}  // namespace
