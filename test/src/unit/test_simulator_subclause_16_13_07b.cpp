#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/local_variable_initialization.sv around one
// property: clk rises at 5, 15, ..., clk1 at 18, 38, ... and clk2 at 22,
// 42, ...; f is high at 5 alone; e is 1 at 5 and at 18 and 0 at 15 and at
// 22; a and b are 1 at 18 alone, c is 1 at 22 alone, d is 0 and g is 1 at
// 15. The assertion counts its passes and failures and keeps the time of
// the last failure.
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

// §16.13.7: the clause's property has two semantic leading clocks, so v is
// copied twice, the clk1 copy initialized at 18, to 1, and the clk2 copy at
// 22, to 0; (a == v)[*1:$] matches at 18 with b holding and c[*1:$] at 22
// with d == v holding, so the attempt of 5 passes with the nine vacuous
// ones.
TEST(LocalVariableInitialization,
     ACopyPerSemanticLeadingClockIsInitializedAtItsTick) {
  Outcome p = OutcomeOf("    logic v = e;\n",
                        "    (@(posedge clk1) (a == v)[*1:$] |-> b)\n"
                        "    and\n"
                        "    (@(posedge clk2) c[*1:$] |-> d == v);\n");
  EXPECT_EQ(p.passes, 10u);
  EXPECT_EQ(p.fails, 0u);
}

// §16.13.7: the clk2 copy is the 0 e holds at 22 and not the 1 it held at
// 18 or at 5, so d != v fails at 22.
TEST(LocalVariableInitialization, TheSecondCopyReadsItsOwnClocksTick) {
  Outcome p = OutcomeOf("    logic v = e;\n",
                        "    (@(posedge clk1) (a == v)[*1:$] |-> b)\n"
                        "    and\n"
                        "    (@(posedge clk2) c[*1:$] |-> d != v);\n");
  EXPECT_EQ(p.passes, 9u);
  EXPECT_EQ(p.fails, 1u);
  EXPECT_EQ(p.failed_at, 22u);
}

// §16.13.7: with clk1 alone as the semantic leading clock, u is
// initialized at 18, the earliest tick of clk1 after the attempt begins at
// 15, to 1 and not to the 0 e holds at 15: (a == u)[*1:$] matches at 18,
// where !b fails.
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

// §16.13.7: a singly clocked property initializes w when the attempt
// begins, at 5, to 1 and not to the 0 e holds at 15: g == w holds at 15 and
// g != w fails there.
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

// §16.10: the initializations are performed in declaration order, one
// reading the locals declared before it, so a second local initialized
// from the first holds the first's value.
TEST(LocalVariableInitialization, ALaterLocalReadsTheCopyOfAnEarlierOne) {
  Outcome q = OutcomeOf("    logic w = e;\n    logic x = w;\n",
                        "    1'b1 ##1 (g == x);\n", "|->");
  EXPECT_EQ(q.passes, 10u);
  EXPECT_EQ(q.fails, 0u);
}

}  // namespace
