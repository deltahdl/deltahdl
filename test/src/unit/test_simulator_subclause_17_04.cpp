#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A checker whose clock and reset formals default to the context value
// functions, its one assertion counting successes and failures.
constexpr const char* kContextChecker =
    "checker chk(logic sig, event clock = $inferred_clock,\n"
    "            logic reset = $inferred_disable);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@clock disable iff (reset) sig) pass++;\n"
    "    else fail++;\n"
    "endchecker\n";

// The successes and failures k's counters hold once `module` has run over
// kContextChecker.
std::pair<uint64_t, uint64_t> ContextCheckerCounts(const std::string& module) {
  SimFixture f;
  auto* pass =
      RunAndFindVar(std::string(kContextChecker) + module, f, "k.pass");
  if (pass == nullptr) return {~0ull, ~0ull};
  return {pass->value.ToUint64(),
          f.ctx.FindVariable("k.fail")->value.ToUint64()};
}

// §17.4 with §16.14.7: an instance leaving both formals to their defaults
// takes the default clocking, posedge clk, and the default disable iff, rst:
// the posedge at 5 is disabled, 15 and 25 fail and 35 and 45 pass. The
// disable default was evaluated at the run as an unknown system function and
// the clock never ticked, so nothing was counted.
TEST(CheckerContextInference, AStaticInstanceTakesTheScopesDefaults) {
  EXPECT_EQ(ContextCheckerCounts(
                "module top;\n"
                "  logic clk = 0, a = 1, rst = 1;\n"
                "  always #5 clk = ~clk;\n"
                "  default clocking @(posedge clk); endclocking\n"
                "  default disable iff rst;\n"
                "  chk k(a);\n"
                "  initial begin #12 begin a = 0; rst = 0; end #20 a = 1;\n"
                "    #20 $finish; end\n"
                "endmodule\n"),
            std::make_pair(2ull, 2ull));
}

// §17.4 with §16.14.6: a procedural instance takes the clock its procedure
// gives, the module declaring no default clocking, and the default disable
// iff, so it counts as the static instance does.
TEST(CheckerContextInference, AProceduralInstanceTakesTheProceduresClock) {
  EXPECT_EQ(ContextCheckerCounts(
                "module top;\n"
                "  logic clk = 0, a = 1, rst = 1;\n"
                "  always #5 clk = ~clk;\n"
                "  default disable iff rst;\n"
                "  always @(posedge clk) begin\n"
                "    chk k(a);\n"
                "  end\n"
                "  initial begin #12 begin a = 0; rst = 0; end #20 a = 1;\n"
                "    #20 $finish; end\n"
                "endmodule\n"),
            std::make_pair(2ull, 2ull));
}

// §16.14.7: outside the scope of any default disable iff, $inferred_disable
// is 1'b0, so the posedge at 5 passes rather than being disabled.
TEST(CheckerContextInference, NoDefaultDisableIffInfersFalse) {
  EXPECT_EQ(ContextCheckerCounts(
                "module top;\n"
                "  logic clk = 0, a = 1;\n"
                "  always #5 clk = ~clk;\n"
                "  default clocking @(posedge clk); endclocking\n"
                "  chk k(a);\n"
                "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
                "endmodule\n"),
            std::make_pair(3ull, 2ull));
}

}  // namespace
