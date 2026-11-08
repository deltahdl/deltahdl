#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Counting(const std::string& decls, const std::string& constraints,
                     int draws, const std::string& holds) {
  return "class C;\n" + decls + constraints +
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

TEST(IterativeConstraintsRun, AForeachConstrainsEveryElement) {
  SimFixture f;
  std::string out = RunCapture(
      Counting(
          "  rand byte A[4];\n",
          "  constraint C1 { foreach (A[i]) A[i] inside {2, 4, 8, 16}; }\n", 32,
          "o.A[0] inside {2, 4, 8, 16} && o.A[1] inside {2, 4, 8, 16} && "
          "o.A[2] inside {2, 4, 8, 16} && o.A[3] inside {2, 4, 8, 16}"),
      f);
  EXPECT_EQ(out, "32\n");
}

TEST(IterativeConstraintsRun, TheLoopVariableIsTheIndex) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] A[4];\n"
      "  constraint C2 { foreach (A[j]) A[j] > 2 * j; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, low = 0;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    repeat (64) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.A[0] > 0 && o.A[1] > 2 && o.A[2] > 4 && o.A[3] > 6) "
      "held++;\n"
      "      if (o.A[0] <= 6) low++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, low > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

TEST(IterativeConstraintsRun, AReductionMethodConstrainsTheArray) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand bit [7:0] B[3];\n",
               "  constraint each { foreach (B[k]) B[k] < 10; }\n"
               "  constraint total { B.sum() == 12; }\n",
               32,
               "o.B[0] + o.B[1] + o.B[2] == 12 && o.B.sum() == 12 && "
               "o.B[0] < 10 && o.B[1] < 10 && o.B[2] < 10"),
      f);
  EXPECT_EQ(out, "32\n");
}

TEST(IterativeConstraintsRun, TheElementsAreHeldOneByOne) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  int v[3];\n"
      "  function void fill(int base);\n"
      "    v[1] = base;\n"
      "    v[2] = v[1] + 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.fill(7);\n"
      "    o.v[2] = o.v[2] * 2;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", o.v[0], o.v[1], o.v[2], "
      "o.v.size(), o.v.sum());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 7 16 3 23\n");
}

}  // namespace
