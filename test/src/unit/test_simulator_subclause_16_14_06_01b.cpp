#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module around the procedures given, as
// test/src/e2e/procedural_assertion_arguments.sv is: clk rises at 5, 15, 25
// and 35, foo holds the even bits of 0 to 10 and bar the bits 0 to 4, i and
// n are static, act is 1 across the tick of 15, w is 1 from 30, and the run
// ends at 40.
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

// §16.14.6.1: the clause's a1 reads the static i as sampled in the Preponed
// region, 0 at the first tick and 10, its value after the loop, at every
// tick after, so its ten instances a tick check foo[0] && bar[0] at the
// first tick and foo[10] && bar[10] after.
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

// §16.14.6.1: the clause's a2 saves const'(i) as the instance is queued, so
// its instances check foo[0] to foo[9] against the sampled bar[i], and a3
// saves both, checking foo[i] && bar[i] for each i.
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

// §16.14.6.1: an automatic variable's immediate value is preserved as a
// const cast's is, so the clause's a4, over the j a for statement declares,
// checks foo[j] && bar[j] for each j as a3 does.
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

// §16.14.6.1: a matured instance holding temporal expressions keeps the
// values it saved for the whole of its evaluation, the procedure's later
// execution affecting nothing of it: the clause's a7 is queued at 15 for k
// of 0 and 1 while act is 1, the instance of 1 holds vacuously there and the
// instance of 0 keeps its k while bar[0] is read at 25 and w at 35.
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

// §16.14.6.1: the same rules apply to the variables of the action block,
// so the clause's a8 reports the const'(n) its instance saved, 1 and 3,
// beside $sampled(n), 0 at the first tick and 4 after.
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

// §16.14.6.1: a conditional around the assertion reads the current values,
// where the assertion's expressions read the sampled ones: the clause's a9
// is queued at the tick en is assigned 1, and a10, under $sampled(en), one
// tick later.
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
