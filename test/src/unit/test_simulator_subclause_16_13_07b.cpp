#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string LocalInitSource(const std::string& locals, const std::string& body,
                            const std::string& implication) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic clk1 = 0;\n"
         "  logic clk2 = 0;\n"
         "  logic f = 1, e = 1, a = 0, b = 0, c = 0, d = 0, g = 0;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int failed_at = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  initial begin\n"
         "    #18;\n"
         "    forever begin\n"
         "      clk1 = 1;\n"
         "      #10 clk1 = 0;\n"
         "      #10;\n"
         "    end\n"
         "  end\n"
         "  initial begin\n"
         "    #22;\n"
         "    forever begin\n"
         "      clk2 = 1;\n"
         "      #10 clk2 = 0;\n"
         "      #10;\n"
         "    end\n"
         "  end\n"
         "  property p;\n" +
         locals + body +
         "  endproperty\n"
         "  assert property (@(posedge clk) f " +
         implication +
         " p) passes++;\n"
         "    else begin\n"
         "      fails++;\n"
         "      failed_at = $time;\n"
         "    end\n"
         "  initial begin\n"
         "    #10 f = 0; e = 0; g = 1;\n"
         "    #6 e = 1; a = 1; b = 1;\n"
         "    #4 e = 0; a = 0; b = 0; g = 0; c = 1;\n"
         "    #4 c = 0;\n"
         "    #76 $finish;\n"
         "  end\n"
         "endmodule\n";
}

struct Outcome {
  uint64_t passes;
  uint64_t fails;
  uint64_t failed_at;
};

Outcome OutcomeOf(const std::string& locals, const std::string& body,
                  const std::string& implication = "|=>") {
  SimFixture f;
  auto* passes =
      RunAndFindVar(LocalInitSource(locals, body, implication), f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  return {passes->value.ToUint64(),
          f.ctx.FindVariable("fails")->value.ToUint64(),
          f.ctx.FindVariable("failed_at")->value.ToUint64()};
}

TEST(LocalVariableInitialization,
     ACopyPerSemanticLeadingClockIsInitializedAtItsTick) {
  Outcome p = OutcomeOf("    logic v = e;\n",
                        "    (@(posedge clk1) (a == v)[*1:$] |-> b)\n"
                        "    and\n"
                        "    (@(posedge clk2) c[*1:$] |-> d == v);\n");
  EXPECT_EQ(p.passes, 10u);
  EXPECT_EQ(p.fails, 0u);
}

TEST(LocalVariableInitialization, TheSecondCopyReadsItsOwnClocksTick) {
  Outcome p = OutcomeOf("    logic v = e;\n",
                        "    (@(posedge clk1) (a == v)[*1:$] |-> b)\n"
                        "    and\n"
                        "    (@(posedge clk2) c[*1:$] |-> d != v);\n");
  EXPECT_EQ(p.passes, 9u);
  EXPECT_EQ(p.fails, 1u);
  EXPECT_EQ(p.failed_at, 22u);
}

TEST(LocalVariableInitialization,
     ASingleLeadingClockInitializesAtItsFirstTick) {
  Outcome r = OutcomeOf("    logic u = e;\n",
                        "    @(posedge clk1) (a == u)[*1:$] |-> b;\n");
  EXPECT_EQ(r.passes, 10u);
  EXPECT_EQ(r.fails, 0u);
  Outcome r_ne = OutcomeOf("    logic u = e;\n",
                           "    @(posedge clk1) (a == u)[*1:$] |-> !b;\n");
  EXPECT_EQ(r_ne.fails, 1u);
  EXPECT_EQ(r_ne.failed_at, 18u);
}

TEST(LocalVariableInitialization,
     ASinglyClockedPropertyInitializesAtTheAttemptsBegin) {
  Outcome q =
      OutcomeOf("    logic w = e;\n", "    1'b1 ##1 (g == w);\n", "|->");
  EXPECT_EQ(q.passes, 10u);
  EXPECT_EQ(q.fails, 0u);
  Outcome q_ne =
      OutcomeOf("    logic w = e;\n", "    1'b1 ##1 (g != w);\n", "|->");
  EXPECT_EQ(q_ne.fails, 1u);
  EXPECT_EQ(q_ne.failed_at, 15u);
}

TEST(LocalVariableInitialization, ALaterLocalReadsTheCopyOfAnEarlierOne) {
  Outcome q = OutcomeOf("    logic w = e;\n    logic x = w;\n",
                        "    1'b1 ##1 (g == x);\n", "|->");
  EXPECT_EQ(q.passes, 10u);
  EXPECT_EQ(q.fails, 0u);
}

}  // namespace
