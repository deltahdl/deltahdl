#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A class C holding the members `decls` under the constraint block `c`,
// randomized `draws` times by an initial that counts the draws for which
// `holds` is true, as the design test/src/e2e/if_else_constraints.sv does,
// and displays the count.
std::string Counting(const std::string& decls, const std::string& constraint,
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

// 18.5.6: the expression of an if-else constraint may be a real
// expression. A real r drawn from 0.5 and 1.5 selects k of 2 above 1.0 and
// of 3 below it on every draw.
TEST(IfElseConstraintsRun, ARealExpressionSelectsTheBranch) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand real r;\n"
               "  rand int k;\n",
               "r dist { 0.5 := 1, 1.5 := 1 }; "
               "if (r > 1.0) k == 2; else k == 3;",
               64, "(o.r > 1.0 && o.k == 2) || (o.r < 1.0 && o.k == 3)"),
      f);
  EXPECT_EQ(out, "64\n");
}

// 18.5.6: the condition and the constraint sets are interdependent, so a
// constraint on len constrains mode: with len held to 50, neither little's
// len below 10 nor big's above 100 can hold, so mode is other, the literal
// of value 2, on every draw.
TEST(IfElseConstraintsRun, TheConstraintSetConstrainsTheCondition) {
  SimFixture f;
  std::string out =
      RunCapture(Counting("  typedef enum {little, big, other} mode_t;\n"
                          "  rand mode_t mode;\n"
                          "  rand int len;\n",
                          "len == 50; if (mode == little) len < 10; "
                          "else if (mode == big) len > 100;",
                          64, "o.mode == 2 && o.len == 50"),
                 f);
  EXPECT_EQ(out, "64\n");
}

// 18.5.6: an else omitted from a nested if sequence goes with the closest
// previous if that lacks one. In the clause's example the else belongs to
// the inner if, so a mode held to big, the literal of value 1, passes the
// outer if and reaches neither set, and len is free to be 50. Were the else
// the outer if's, big would demand len above 100 and randomize() would
// refuse the 50.
TEST(IfElseConstraintsRun, TheElseGoesWithTheClosestIfLackingOne) {
  SimFixture f;
  std::string out =
      RunCapture(Counting("  typedef enum {little, big, other} mode_t;\n"
                          "  rand mode_t mode;\n"
                          "  rand int len;\n",
                          "mode == big; len == 50; "
                          "if (mode != big) if (mode == little) len < 10; "
                          "else len > 100;",
                          32, "o.mode == 1 && o.len == 50"),
                 f);
  EXPECT_EQ(out, "32\n");
}

}  // namespace
