#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kContextChecker =
    "checker chk(logic sig, event clock = $inferred_clock,\n"
    "            logic reset = $inferred_disable);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@clock disable iff (reset) sig) pass++;\n"
    "    else fail++;\n"
    "endchecker\n";

std::pair<uint64_t, uint64_t> ContextCheckerCounts(const std::string& module) {
  SimFixture f;
  auto* pass =
      RunAndFindVar(std::string(kContextChecker) + module, f, "k.pass");
  if (pass == nullptr) return {~0ull, ~0ull};
  return {pass->value.ToUint64(),
          f.ctx.FindVariable("k.fail")->value.ToUint64()};
}

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
