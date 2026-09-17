#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A class C holding the members `decls`, randomized `draws` times by an
// initial that counts the draws for which `holds` is true after `prepare`
// has run, as the design test/src/e2e/array_reduction_constraints.sv does,
// and displays the count and `after`, an expression read once the draws are
// done.
std::string Counting(const std::string& decls, int draws,
                     const std::string& prepare, const std::string& holds,
                     const std::string& after) {
  return "class C;\n" + decls +
         "endclass\n"
         "module t;\n"
         "  int held = 0, total = 0;\n"
         "  initial begin\n"
         "    C o = new;\n"
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

// 18.5.7.2: the clause's example, a dynamic byte array held to five elements
// whose sum through int'(item) is held below a bound: the result is of the
// type of the with clause's expression, an int, so the sum of the five bytes
// stays below 300 on every one of 64 draws, which a sum held to the element
// type, wrapped to a byte and so below 300 whatever the elements, would not
// give, and the elements are drawn, some draw summing above 100.
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

// 18.5.7.2: without a with clause the result is of the element type, so a
// sum of three bytes held to 44 wraps to the byte: with each element from 100
// to 200 the elements sum to 300 or 556, which is 44 as a byte, on every one
// of 64 draws.
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

// 18.5.7.2: the size constraints are solved first and the reduction next, so
// a dynamic array drawn at two to six elements has the elements drawn, and
// those alone, summing to 100 through int'(item) on every one of 64 draws,
// over more than one size.
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
      "    C o = new;\n"
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

// 18.5.7.2: each element is joined by the operand of the method, so product()
// multiplies: three 4-bit elements from 2 to 5 held to a product of 8
// multiply to 8 or 40, which is 8 as a nibble, on every one of 64 draws.
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

// 18.5.7.2: the reduction reads the elements the object holds as well as
// the solver's draws: a sum through a with clause over an array sized and
// filled by a method, read outside any randomize(), is the sum the clause
// interprets, int'(A[0]) + ... + int'(A[4]), here 15 as an int, where the
// bytes' own sum wrapped would read 15 as well and a product through the
// clause reads 120.
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
      "    C o = new;\n"
      "    o.fill();\n"
      "    $display(\"%0d %0d\", o.total(), o.product());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "15 120\n");
}

}  // namespace
