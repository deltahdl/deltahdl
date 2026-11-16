#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Randomized(const std::string& cls,
                       const std::vector<std::string>& shown) {
  std::string format = "%0d";
  std::string args = "ok";
  for (const auto& name : shown) {
    format += " %0d";
    args += ", o." + name;
  }
  return cls +
         "module t;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    automatic int ok = o.randomize();\n"
         "    $display(\"" +
         format + "\", " + args +
         ");\n"
         "  end\n"
         "endmodule\n";
}

TEST(RandomArrayElements, OneElementIndexedByALiteralIsMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  constraint c { a[1] == 77; }\n"
                                  "endclass\n",
                                  {"a[1]"}),
                       f),
            "1 77\n");
}

TEST(RandomArrayElements, OneElementIndexedByAStateVariableIsMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  int k = 2;\n"
                                  "  constraint c { a[k] == 77; }\n"
                                  "endclass\n",
                                  {"a[2]"}),
                       f),
            "1 77\n");
}

TEST(RandomArrayElements, OneElementIndexedByALocalparamIsMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  localparam int P = 3;\n"
                                  "  constraint c { a[P] == 9; }\n"
                                  "endclass\n",
                                  {"a[3]"}),
                       f),
            "1 9\n");
}

TEST(RandomArrayElements, LoopVariableIndexedElementsOfEveryArrayKindAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[3];\n"
                                  "  rand bit [7:0] d[];\n"
                                  "  rand bit [7:0] q[$];\n"
                                  "  constraint c { d.size() == 3; "
                                  "q.size() == 3;\n"
                                  "    foreach (a[i]) a[i] == i + 4;\n"
                                  "    foreach (d[i]) d[i] == i + 5;\n"
                                  "    foreach (q[i]) q[i] == i + 6; }\n"
                                  "endclass\n",
                                  {"a[0]", "a[1]", "a[2]", "d[0]", "d[1]",
                                   "d[2]", "q[0]", "q[1]", "q[2]"}),
                       f),
            "1 4 5 6 5 6 7 6 7 8\n");
}

TEST(RandomArrayElements, DISABLED_TwoLiteralIndexedElementsInOneBlockAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  constraint c { a[1] == 7; a[2] == 5; }\n"
                                  "endclass\n",
                                  {"a[1]", "a[2]"}),
                       f),
            "1 7 5\n");
}

TEST(RandomArrayElements, DISABLED_TwoLiteralIndexedElementsInTwoBlocksAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  constraint c { a[1] == 7; }\n"
                                  "  constraint d { a[2] == 5; }\n"
                                  "endclass\n",
                                  {"a[1]", "a[2]"}),
                       f),
            "1 7 5\n");
}

TEST(RandomArrayElements, DISABLED_TwoElementsOfADynamicArrayAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[];\n"
                                  "  constraint c { a.size() == 4; a[1] == 7; "
                                  "a[2] == 5; }\n"
                                  "endclass\n",
                                  {"a.size()", "a[1]", "a[2]"}),
                       f),
            "1 4 7 5\n");
}

TEST(RandomArrayElements, DISABLED_TwoElementsOfAQueueAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[$];\n"
                                  "  constraint c { a.size() == 4; a[1] == 7; "
                                  "a[2] == 5; }\n"
                                  "endclass\n",
                                  {"a.size()", "a[1]", "a[2]"}),
                       f),
            "1 4 7 5\n");
}

TEST(RandomArrayElements, DISABLED_TwoElementsOfATwoDimensionalArrayAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[2][2];\n"
                                  "  constraint c { a[0][1] == 7; "
                                  "a[1][0] == 5; }\n"
                                  "endclass\n",
                                  {"a[0][1]", "a[1][0]"}),
                       f),
            "1 7 5\n");
}

TEST(RandomArrayElements, DISABLED_OneElementRelatedToAnotherIsMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  constraint c { a[1] == a[0] + 1; "
                                  "a[0] == 3; }\n"
                                  "endclass\n",
                                  {"a[0]", "a[1]"}),
                       f),
            "1 3 4\n");
}

TEST(RandomArrayElements, DISABLED_TwoStateVariableIndexedElementsAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  int k = 1;\n"
                                  "  constraint c { a[k] == 77; "
                                  "a[k+1] == 5; }\n"
                                  "endclass\n",
                                  {"a[1]", "a[2]"}),
                       f),
            "1 77 5\n");
}

TEST(RandomArrayElements, DISABLED_TwoLocalparamIndexedElementsAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  localparam int P = 2;\n"
                                  "  constraint c { a[P] == 9; "
                                  "a[P-1] == 8; }\n"
                                  "endclass\n",
                                  {"a[1]", "a[2]"}),
                       f),
            "1 8 9\n");
}

TEST(RandomArrayElements, DISABLED_ElementsConstrainedInlineAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  rand bit [7:0] a[4];\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    automatic int ok = o.randomize() with "
                       "{ a[1] == 7; a[2] == 5; };\n"
                       "    $display(\"%0d %0d %0d\", ok, o.a[1], o.a[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 7 5\n");
}

TEST(RandomArrayElements, DISABLED_ElementsConstrainedOutOfBlockAreMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Randomized("class C;\n"
                                  "  rand bit [7:0] a[4];\n"
                                  "  extern constraint c;\n"
                                  "endclass\n"
                                  "constraint C::c { a[1] == 7; a[2] == 5; }\n",
                                  {"a[1]", "a[2]"}),
                       f),
            "1 7 5\n");
}

TEST(RandomArrayElements, AContradictionOnOneElementFails) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  rand bit [7:0] a[4];\n"
                       "  constraint c { a[1] == 7; a[1] == 8; }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    o.a[1] = 42;\n"
                       "    $display(\"%0d %0d\", o.randomize(), o.a[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 42\n");
}

}  // namespace
