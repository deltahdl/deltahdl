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

// A class holding the one member `decl` and the constraint `constraint`,
// randomized 8 times by an initial that counts the calls answering 1.
std::string Lone(const std::string& decl, const std::string& constraint) {
  return "class Lone;\n" + decl + constraint +
         "endclass\n"
         "module t;\n"
         "  initial begin\n"
         "    Lone o = new;\n"
         "    int n = 0;\n"
         "    repeat (8) if (o.randomize() == 1) n++;\n"
         "    $display(\"%0d\", n);\n"
         "  end\n"
         "endmodule\n";
}

// §18.4.1: a rand real member alone, under its range constraint, is drawn
// eight times over.
TEST(RandomVariableRun, ALoneRealMemberIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Lone("  rand real r;\n",
                            "  constraint cr { r > 0.0 && r < 2.0; }\n"),
                       f),
            "8\n");
}

// §18.4.2: a randc member alone is drawn eight times over, two cycles of
// its four values.
TEST(RandomVariableRun, ALoneRandcMemberIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Lone("  randc bit [1:0] c;\n", ""), f), "8\n");
}

// §18.4: a rand packed structure with an enum member, and a rand enum, are
// drawn eight times over.
TEST(RandomVariableRun, LoneEnumAndPackedStructMembersAreDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef enum bit [1:0] {A = 2'b00, B = 2'b11} ab_e;\n"
                       "typedef struct packed {\n"
                       "  ab_e ValidAB;\n"
                       "} VStructEnum;\n" +
                           Lone("  rand ab_e e;\n  rand VStructEnum s;\n", ""),
                       f),
            "8\n");
}

// §18.4: a rand object handle whose object carries a constraint, under a
// global constraint of the holder's, is solved eight times over.
TEST(RandomVariableRun, ALoneRandHandleIsSolvedWithTheHolder) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Inner;\n"
                       "  rand int v;\n"
                       "  constraint cv { v inside {[1:3]}; }\n"
                       "endclass\n" +
                           Lone("  rand Inner in;\n  rand bit [3:0] w;\n"
                                "  function new();\n    in = new;\n"
                                "  endfunction\n",
                                "  constraint cw { w > in.v; }\n"),
                       f),
            "8\n");
}

// The Inner of the design and a Lone holding a rand handle to it beside
// `decl`, under the handle's global constraint and `constraint`.
std::string WithHandle(const std::string& decl, const std::string& constraint) {
  return "class Inner;\n"
         "  rand int v;\n"
         "  constraint cv { v inside {[1:3]}; }\n"
         "endclass\n" +
         Lone("  rand Inner in;\n  rand bit [3:0] w;\n" + decl +
                  "  function new();\n    in = new;\n  endfunction\n",
              "  constraint cw { w > in.v; }\n" + constraint);
}

// §18.4: a rand real beside a rand handle is solved with the handle's
// object eight times over.
TEST(RandomVariableRun, ARealBesideARandHandleIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(WithHandle("  rand real r;\n",
                                  "  constraint cr { r > 0.0 && r < 2.0; }\n"),
                       f),
            "8\n");
}

// §18.4: a randc beside a rand handle is drawn eight times over.
TEST(RandomVariableRun, ARandcBesideARandHandleIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(WithHandle("  randc bit [1:0] c;\n", ""), f), "8\n");
}

// §18.4: a rand enum and a rand packed structure beside a rand handle are
// drawn eight times over.
TEST(RandomVariableRun, AnEnumAndAPackedStructBesideARandHandleAreDrawn) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("typedef enum bit [1:0] {A = 2'b00, B = 2'b11} ab_e;\n"
                 "typedef struct packed {\n"
                 "  ab_e ValidAB;\n"
                 "} VStructEnum;\n" +
                     WithHandle("  rand ab_e e;\n  rand VStructEnum s;\n", ""),
                 f),
      "8\n");
}

// §18.4: a rand real beside a randc is drawn eight times over.
TEST(RandomVariableRun, ARealBesideARandcIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Lone("  rand real r;\n  randc bit [1:0] c;\n",
                            "  constraint cr { r > 0.0 && r < 2.0; }\n"),
                       f),
            "8\n");
}

}  // namespace
