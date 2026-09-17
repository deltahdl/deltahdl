#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A class C holding the members `decls` under the constraint block `c`,
// randomized `draws` times by an initial that counts the draws for which
// `holds` is true, as the design test/src/e2e/implication_constraints.sv
// does, and displays the count.
std::string Design(const std::string& decls, const std::string& constraint,
                   int draws, const std::string& holds) {
  return "class C;\n" + decls + "  constraint c { " + constraint +
         " }\n"
         "endclass\n"
         "module t;\n"
         "  int held = 0;\n"
         "  initial begin\n"
         "    C o = new;\n"
         "    repeat (" +
         std::to_string(draws) +
         ") begin\n"
         "      void'(o.randomize());\n"
         "      if (" +
         holds +
         ") held++;\n"
         "    end\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

// 18.5.5: the expression implying a constraint may be a real expression. A
// real r drawn from 0.5 and 1.5 implies k of 3 below 1.0 and 2 above it on
// every draw. The relation read a real variable as 0 for want of its draw,
// which the solver keeps apart from the integral draws it handed over, so
// the antecedent over r never held and k went free.
TEST(ImplicationConstraintsRun, ARealExpressionImpliesTheConsequent) {
  SimFixture f;
  std::string out = RunCapture(
      Design("  rand real r;\n"
             "  rand int k;\n",
             "r dist { 0.5 := 1, 1.5 := 1 }; (r > 1.0) -> k == 2; "
             "(r < 1.0) -> k == 3;",
             64, "(o.r > 1.0 && o.k == 2) || (o.r < 1.0 && o.k == 3)"),
      f);
  EXPECT_EQ(out, "64\n");
}

// 18.5.5: the two sides of an implication are interdependent, so a
// constraint on the consequent's variable constrains the expression's: with
// len held to 50, neither little's len below 10 nor big's above 100 can
// hold, so mode is never little nor big but other, the literal of value 2.
TEST(ImplicationConstraintsRun, TheConsequentConstrainsTheExpression) {
  SimFixture f;
  std::string out =
      RunCapture(Design("  typedef enum {little, big, other} mode_t;\n"
                        "  rand mode_t mode;\n"
                        "  rand int len;\n",
                        "len == 50; (mode == little) -> len < 10; "
                        "(mode == big) -> len > 100;",
                        64, "o.mode == 2 && o.len == 50"),
                 f);
  EXPECT_EQ(out, "64\n");
}

// 18.5.5: the clause's 4-bit a and b under (a == 0) -> (b == 1) leave 241
// of the 256 combinations, each as likely as another, so a == 0 is drawn
// about once in 241 draws: over 4820 draws some tens of times, where a
// draw of a alone would give it a sixteenth, about 300.
TEST(ImplicationConstraintsRun, TheExpressionIsAsLikelyAsItsCombinations) {
  SimFixture f;
  std::string out =
      RunCapture(Design("  rand bit [3:0] a;\n"
                        "  rand bit [3:0] b;\n",
                        "(a == 0) -> (b == 1);", 4820, "o.a == 0"),
                 f);
  int zeros = std::stoi(out);
  EXPECT_GT(zeros, 0);
  EXPECT_LT(zeros, 100);
}

}  // namespace
