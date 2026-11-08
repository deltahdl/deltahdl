#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string ArgumentsSource(const std::string& procedures) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic [10:0] foo = 11'b10101010101, bar = 11'b00000011111;\n"
         "  logic w = 0, act = 0, en = 0;\n"
         "  int i, n, cyc = 0;\n"
         "  int passes = 0, fails = 0, first = 0, last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         procedures +
         "  initial begin\n"
         "    #12 act = 1;\n"
         "    #6 act = 0;\n"
         "    #12 w = 1;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

uint64_t Count(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? 0 : var->value.ToUint64();
}

TEST(ProceduralAssertionArgumentsRun, AStaticVariableIsReadSampled) {
  SimFixture f;
  RunAndFindVar(ArgumentsSource("  always @(posedge clk)\n"
                                "    for (i = 0; i < 10; i++)\n"
                                "      a1: assert property (foo[i] && bar[i])\n"
                                "        passes++; else fails++;\n"),
                f, "passes");
  EXPECT_EQ(Count(f, "passes"), 10u);
  EXPECT_EQ(Count(f, "fails"), 30u);
}

TEST(ProceduralAssertionArgumentsRun, AConstCastIsSavedAsTheInstanceIsQueued) {
  SimFixture f;
  RunAndFindVar(
      ArgumentsSource("  always @(posedge clk)\n"
                      "    for (i = 0; i < 10; i++)\n"
                      "      a2: assert property (foo[const'(i)] && bar[i])\n"
                      "        passes++; else fails++;\n"),
      f, "passes");
  EXPECT_EQ(Count(f, "passes"), 5u);
  EXPECT_EQ(Count(f, "fails"), 35u);
  SimFixture g;
  RunAndFindVar(ArgumentsSource("  always @(posedge clk)\n"
                                "    for (i = 0; i < 10; i++)\n"
                                "      a3: assert property\n"
                                "        (foo[const'(i)] && bar[const'(i)])\n"
                                "        passes++; else fails++;\n"),
                g, "passes");
  EXPECT_EQ(Count(g, "passes"), 12u);
  EXPECT_EQ(Count(g, "fails"), 28u);
}

TEST(ProceduralAssertionArgumentsRun, AnAutomaticVariableIsSavedLikewise) {
  SimFixture f;
  RunAndFindVar(ArgumentsSource("  always @(posedge clk)\n"
                                "    for (int j = 0; j < 10; j++)\n"
                                "      a4: assert property (foo[j] && bar[j])\n"
                                "        passes++; else fails++;\n"),
                f, "passes");
  EXPECT_EQ(Count(f, "passes"), 12u);
  EXPECT_EQ(Count(f, "fails"), 28u);
}

TEST(ProceduralAssertionArgumentsRun, AMaturedInstanceKeepsItsSavedValues) {
  SimFixture f;
  RunAndFindVar(
      ArgumentsSource("  always @(posedge clk) begin : procedural_block_1\n"
                      "    if (act == 1)\n"
                      "      for (int k = 0; k < 2; k++)\n"
                      "        a7: assume property\n"
                      "          (foo[k] |=> bar[k] ##1 (w == 1'b1)) begin\n"
                      "          passes++;\n"
                      "          if (passes == 1) first = $time;\n"
                      "          else last = $time;\n"
                      "        end else fails++;\n"
                      "  end\n"),
      f, "passes");
  EXPECT_EQ(Count(f, "passes"), 2u);
  EXPECT_EQ(Count(f, "fails"), 0u);
  EXPECT_EQ(Count(f, "first"), 15u);
  EXPECT_EQ(Count(f, "last"), 35u);
}

TEST(ProceduralAssertionArgumentsRun, TheActionBlockReadsTheSavedValues) {
  SimFixture f;
  std::string out =
      RunCapture(ArgumentsSource(
                     "  always @(posedge clk)\n"
                     "    for (n = 0; n < 4; n++)\n"
                     "      a8: assert property (foo[const'(n)] && bar[n])\n"
                     "        else $display(\"const n=%0d n=%0d\", const'(n),\n"
                     "                      $sampled(n));\n"),
                 f);
  EXPECT_EQ(out,
            "const n=1 n=0\nconst n=3 n=0\nconst n=1 n=4\nconst n=3 n=4\n"
            "const n=1 n=4\nconst n=3 n=4\nconst n=1 n=4\nconst n=3 n=4\n"
            "$finish at time 40\n");
}

TEST(ProceduralAssertionArgumentsRun, AConditionalReadsTheCurrentValue) {
  SimFixture f;
  std::string out = RunCapture(
      ArgumentsSource("  always @(posedge clk) begin\n"
                      "    cyc++;\n"
                      "    en = (cyc == 2);\n"
                      "    if (en) a9: assert property (1)\n"
                      "      $display(\"a9 at %0d\", $time);\n"
                      "    if ($sampled(en)) a10: assert property (1)\n"
                      "      $display(\"a10 at %0d\", $time);\n"
                      "  end\n"),
      f);
  EXPECT_EQ(out, "a9 at 15\na10 at 25\n$finish at time 40\n");
}

}  // namespace
