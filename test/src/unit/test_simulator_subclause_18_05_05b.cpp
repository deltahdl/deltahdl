#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& decls, const std::string& constraint,
                   int draws, const std::string& holds) {
  return "class C;\n" + decls + "  constraint c { " + constraint +
         " }\n"
         "endclass\n"
         "module t;\n"
         "  int held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
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
