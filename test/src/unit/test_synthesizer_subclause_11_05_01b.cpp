#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

void ExpectSelectAgrees(const std::string& data_range,
                        const std::string& y_range,
                        const std::string& select_expr, uint64_t input_word) {
  std::string dut = "module m(input " + data_range + " data, output " +
                    y_range + " y);\n  assign y = " + select_expr +
                    ";\nendmodule\n";
  SCOPED_TRACE(dut);
  SCOPED_TRACE("input word " + std::to_string(input_word));

  SynthFixture synth_fixture;
  const auto* mod = ElaborateSrc(synth_fixture, dut);
  ASSERT_NE(mod, nullptr);
  SynthLower synth(synth_fixture.arena, synth_fixture.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  uint64_t synthesized = EvalAigOutputs(*aig, input_word);

  std::string tb = dut + "module top;\n  wire " + data_range +
                   " drv;\n  wire " + y_range + " result;\n" +
                   "  assign drv = 8'd" + std::to_string(input_word) +
                   ";\n  m u(.data(drv), .y(result));\nendmodule\n";
  SimFixture sim_fixture;
  auto* simulated = RunAndFindVar(tb, sim_fixture, "result");
  ASSERT_NE(simulated, nullptr);
  EXPECT_EQ(synthesized, simulated->value.ToUint64());
}

TEST(SelectAgreement, BitSelectReachesTheSameBitInBothComponents) {
  ExpectSelectAgrees("[8:1]", "", "data[3]", 0xA5);
}

TEST(SelectAgreement, AscendingDeclarationReachesTheSameBitInBothComponents) {
  ExpectSelectAgrees("[1:8]", "", "data[3]", 0x0C);
}

TEST(SelectAgreement, IndexedPartSelectPlusCoversTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[8:1]", "[3:0]", "data[2 +: 4]", 0xA5);
}

TEST(SelectAgreement, IndexedPartSelectMinusCoversTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[8:1]", "[3:0]", "data[8 -: 4]", 0xA5);
}

TEST(SelectAgreement,
     AscendingIndexedPartSelectCoversTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[1:8]", "[3:0]", "data[2 +: 4]", 0xA5);
}

TEST(SelectAgreement,
     PartSelectRunningOffTheTopReadsTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[8:1]", "[4:0]", "data[10:6]", 0xA5);
}

}  // namespace
