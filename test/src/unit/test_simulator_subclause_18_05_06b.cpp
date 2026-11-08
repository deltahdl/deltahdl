#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Counting(const std::string& decls, const std::string& constraint,
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
