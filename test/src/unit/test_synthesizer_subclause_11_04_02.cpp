#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

std::string AlwaysCombEndingIn(std::string_view stmt) {
  return std::string(
             "module m(input [3:0] a, output logic [3:0] y);\n"
             "  always_comb begin\n"
             "    y = a;\n"
             "    ") +
         std::string(stmt) +
         ";\n"
         "  end\n"
         "endmodule\n";
}

void ExpectAlwaysCombSweep(std::string_view stmt,
                           uint64_t (*expected)(uint64_t)) {
  SCOPED_TRACE(std::string(stmt));
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, AlwaysCombEndingIn(stmt));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t a = 0; a < 16; ++a) {
    EXPECT_EQ(EvalAigOutputs(*aig, a), expected(a)) << "a = " << a;
  }
}

TEST(IncrementSynthesis, PostfixIncrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("y++", [](uint64_t a) { return (a + 1) & 0xFU; });
}

TEST(IncrementSynthesis, PrefixIncrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("++y", [](uint64_t a) { return (a + 1) & 0xFU; });
}

TEST(IncrementSynthesis, DecrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("y--", [](uint64_t a) { return (a - 1) & 0xFU; });
}

TEST(IncrementSynthesis, PrefixDecrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("--y", [](uint64_t a) { return (a - 1) & 0xFU; });
}

TEST(IncrementSynthesis, IncrementOfABitSelectIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, AlwaysCombEndingIn("y[0]++"));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "statement has no lowering in the synthesizer "
                            "and would be dropped from the netlist",
                            4, ""));
}

TEST(IncrementSynthesis,
     ExpressionStatementWithoutAnIncrementIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  task t();\n"
                   "  endtask\n"
                   "  always_comb begin\n"
                   "    y = a;\n"
                   "    t();\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "statement has no lowering in the synthesizer "
                            "and would be dropped from the netlist",
                            6, ""));
}

TEST(IncrementSynthesis,
     PostfixIncrementInsideAnExpressionIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  logic [3:0] i;\n"
                   "  always_comb begin\n"
                   "    i = a;\n"
                   "    y = (i++) + 1;\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "postfix increment or decrement operator written inside an expression", 5,
      "11.4.2"));
}

}  // namespace
