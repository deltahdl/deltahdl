#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Counting(const std::string& decls, int draws,
                     const std::string& prepare, const std::string& holds,
                     const std::string& after) {
  return "class C;\n" + decls +
         "endclass\n"
         "module t;\n"
         "  int held = 0, total = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    repeat (" +
         std::to_string(draws) +
         ") begin\n"
         "      void'(o.randomize());\n" +
         prepare + "      if (" + holds +
         ") held++;\n"
         "    end\n"
         "    $display(\"%0d %0d\", held, " +
         after +
         ");\n"
         "  end\n"
         "endmodule\n";
}

TEST(ArrayReductionConstraintsRun, AWithClauseTypesTheResult) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand bit [7:0] A[];\n"
               "  constraint c1 { A.size == 5; }\n"
               "  constraint c2 { A.sum() with (int'(item)) < 300; }\n",
               64,
               "      total = o.A[0] + o.A[1] + o.A[2] + o.A[3] + o.A[4];\n"
               "      if (total > 100) held = held + 1000;\n",
               "o.A.size() == 5 && total < 300", "held > 1000"),
      f);
  EXPECT_EQ(out.substr(out.find(' ')), " 1\n");
  EXPECT_EQ(std::stoi(out) % 1000, 64);
}

TEST(ArrayReductionConstraintsRun, TheResultIsOfTheElementType) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand bit [7:0] B[3];\n"
               "  constraint each { foreach (B[i]) B[i] inside {[100:200]}; }\n"
               "  constraint total { B.sum() == 44; }\n",
               64, "      total = o.B[0] + o.B[1] + o.B[2];\n",
               "total % 256 == 44 && o.B[0] >= 100 && o.B[1] >= 100 && "
               "o.B[2] >= 100 && o.B[0] <= 200 && o.B[1] <= 200 && o.B[2] <= "
               "200",
               "total > 44"),
      f);
  EXPECT_EQ(out, "64 1\n");
}

TEST(ArrayReductionConstraintsRun, TheSizeIsSolvedBeforeTheReduction) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] C[];\n"
      "  constraint c1 { C.size inside {[2:6]}; }\n"
      "  constraint c2 { C.sum() with (int'(item)) == 100; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, total = 0, smallest = 7, largest = 0;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    repeat (64) begin\n"
      "      void'(o.randomize());\n"
      "      total = 0;\n"
      "      for (int i = 0; i < o.C.size(); i++) total = total + o.C[i];\n"
      "      if (o.C.size() >= 2 && o.C.size() <= 6 && total == 100) held++;\n"
      "      if (o.C.size() < smallest) smallest = o.C.size();\n"
      "      if (o.C.size() > largest) largest = o.C.size();\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, largest > smallest);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

TEST(ArrayReductionConstraintsRun, AProductJoinsByMultiplication) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand bit [3:0] D[3];\n"
               "  constraint each { foreach (D[i]) D[i] inside {[2:5]}; }\n"
               "  constraint total { D.product() == 8; }\n",
               64,
               "      total = o.D[0];\n"
               "      total = total * o.D[1];\n"
               "      total = total * o.D[2];\n",
               "total % 16 == 8 && o.D[0] >= 2 && o.D[1] >= 2 && o.D[2] >= 2 "
               "&& o.D[0] <= 5 && o.D[1] <= 5 && o.D[2] <= 5",
               "total > 0"),
      f);
  EXPECT_EQ(out, "64 1\n");
}

TEST(ArrayReductionConstraintsRun, AWithClauseIsReadOnTheObject) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  bit [7:0] A[];\n"
      "  function void fill();\n"
      "    A = new[5];\n"
      "    for (int i = 0; i < 5; i++) A[i] = i + 1;\n"
      "  endfunction\n"
      "  function int total();\n"
      "    return A.sum() with (int'(item));\n"
      "  endfunction\n"
      "  function int product();\n"
      "    return A.product() with (int'(item));\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.fill();\n"
      "    $display(\"%0d %0d\", o.total(), o.product());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "15 120\n");
}

}  // namespace
