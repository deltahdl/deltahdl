#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The Vars of test/src/e2e/random_variables.sv, an object holding one
// random variable per rule of the clause, around the statements of an
// initial that holds it as vars, its Inner as held and the ints n and m.
std::string Design(const std::string& body) {
  return "typedef enum bit [1:0] {A = 2'b00, B = 2'b11} ab_e;\n"
         "typedef struct packed {\n"
         "  ab_e ValidAB;\n"
         "} VStructEnum;\n"
         "class Inner;\n"
         "  rand int v;\n"
         "  constraint cv { v inside {[1:3]}; }\n"
         "endclass\n"
         "class Vars;\n"
         "  rand bit [7:0] y;\n"
         "  randc bit [1:0] c;\n"
         "  rand real r;\n"
         "  rand ab_e e;\n"
         "  rand VStructEnum s;\n"
         "  rand Inner in;\n"
         "  rand bit [3:0] w;\n"
         "  constraint cr { r > 0.0 && r < 2.0; }\n"
         "  constraint cw { w > in.v; }\n"
         "  function new();\n"
         "    in = new;\n"
         "  endfunction\n"
         "endclass\n"
         "module t;\n"
         "  initial begin\n"
         "    Vars vars = new;\n"
         "    Inner held = vars.in;\n"
         "    int n = 0, m = 0;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// §18.4.2: a randc variable cycles through all the values of its declared
// range in a random permutation, so each group of four randomizations of
// the 2-bit c visits every value once; §18.4.1 has the 8-bit y stay within
// 0 to 255 and every randomize() succeed.
TEST(RandomVariableRun, ARandcVariableCyclesThroughItsRange) {
  SimFixture f;
  std::string out = RunCapture(
      Design("    bit [3:0] seen;\n"
             "    repeat (10) begin\n"
             "      seen = 0;\n"
             "      repeat (4) begin\n"
             "        if (vars.randomize() == 1 && vars.y <= 255) n++;\n"
             "        seen[vars.c] = 1;\n"
             "      end\n"
             "      if (seen == 4'b1111) m++;\n"
             "    end\n"
             "    $display(\"%0d %0d\", n, m);\n"),
      f);
  EXPECT_EQ(out, "40 10\n");
}

// §18.4.1: a real random variable is uniformly distributed over the range
// its constraints leave, here 0.0 to 2.0, which every randomization
// respects; §18.3's enum rule holds e to A or B while the packed struct s,
// treated as an integral type, has its enum member take 2'b01 or 2'b10 as
// well over 40 draws.
TEST(RandomVariableRun, RealsEnumsAndPackedStructsDrawAsTheClauseHasIt) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    repeat (40) begin\n"
                        "      void'(vars.randomize());\n"
                        "      if (vars.r > 0.0 && vars.r < 2.0 && "
                        "(vars.e == A || vars.e == B)) n++;\n"
                        "      if (vars.s != 2'b00 && vars.s != 2'b11) m++;\n"
                        "    end\n"
                        "    $display(\"%0d %0d\", n, m > 0);\n"),
                 f);
  EXPECT_EQ(out, "40 1\n");
}

// §18.4: an object handle declared rand has the object's variables and
// constraints solved concurrently with the holder's, in.v under its own
// range and w above it under the holder's global constraint, and the
// handle itself is never modified.
TEST(RandomVariableRun, ARandHandlesObjectIsSolvedWithTheHolder) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    repeat (40) begin\n"
                        "      void'(vars.randomize());\n"
                        "      if (vars.in.v >= 1 && vars.in.v <= 3 && "
                        "vars.w > vars.in.v) n++;\n"
                        "      if (vars.in == held) m++;\n"
                        "    end\n"
                        "    $display(\"%0d %0d\", n, m);\n"),
                 f);
  EXPECT_EQ(out, "40 40\n");
}

}  // namespace
