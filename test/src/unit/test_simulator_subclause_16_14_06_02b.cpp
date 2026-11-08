#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"

using namespace delta;

namespace {

std::string FlushSource(const std::string& procedures) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0, not_a;\n"
         "  logic a2_a = 0, a2_b = 0;\n"
         "  logic src = 0, ca, cb;\n"
         "  int passes = 0, fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  assign not_a = !a;\n"
         "  assign ca = src;\n"
         "  assign cb = src;\n"
         "  default clocking @(posedge clk); endclocking\n" +
         procedures +
         "  initial begin\n"
         "    #10 a2_a = 1;\n"
         "    #5 a = 1;\n"
         "    #5 a = 0;\n"
         "    #5 src = 1;\n"
         "    #10 src = 0;\n"
         "    #15 $finish;\n"
         "  end\n"
         "endmodule\n";
}

uint64_t Count(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? 0 : var->value.ToUint64();
}

TEST(ProceduralAssertionFlushPointsRun,
     AnAlwaysCombResumingOnADependentSignalFlushesTheStaleInstance) {
  SimFixture f;
  RunAndFindVar(FlushSource("  always_comb begin : b1\n"
                            "    a1: assert property (const'(not_a) != "
                            "const'(a)) passes++;\n"
                            "    else fails++;\n"
                            "  end\n"),
                f, "passes");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "passes"), 3u);
  EXPECT_EQ(Count(f, "fails"), 0u);
}

TEST(ProceduralAssertionFlushPointsRun,
     ResumingAtAnEventControlFlushesWhatADelayLetMature) {
  SimFixture f;
  std::string out = RunCapture(
      FlushSource("  always @(a2_a or a2_b) begin : b2\n"
                  "    a2: assert property (const'(a2_a) == const'(a2_b))\n"
                  "      $display(\"a2 passed at %0d\", $time);\n"
                  "    else $display(\"a2 failed at %0d\", $time);\n"
                  "    #1;\n"
                  "    a3: assert property (const'(a2_a) == const'(a2_b))\n"
                  "      $display(\"a3 passed at %0d\", $time);\n"
                  "    else $display(\"a3 failed at %0d\", $time);\n"
                  "    a2_b <= a2_a;\n"
                  "  end\n"),
      f);
  EXPECT_EQ(out,
            "a2 failed at 15\na2 passed at 15\na3 passed at 15\n"
            "$finish at time 50\n");
}

TEST(ProceduralAssertionFlushPointsRun, AFlushedGlitchIsNeverCovered) {
  SimFixture f;
  RunAndFindVar(FlushSource("  always_comb begin : b3\n"
                            "    c1: cover property (const'(cb) != "
                            "const'(ca));\n"
                            "  end\n"),
                f, "passes");
  const auto& results = f.ctx.ConcurrentCovers().Results();
  ASSERT_EQ(results.size(), 1u);
  EXPECT_EQ(results[0].scope, "t.b3.c1");
  EXPECT_EQ(results[0].attempted, 3u);
  EXPECT_EQ(results[0].succeeded, 0u);
}

}  // namespace
