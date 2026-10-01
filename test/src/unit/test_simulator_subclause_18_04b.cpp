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

// §18.4: a rand packed structure is one integral random variable, and a
// constraint on one of its members constrains that member's bits of it: hi
// is held at A and lo drawn from 1 to 3, so the whole lies in A1 to A3.
TEST(RandPackedStructRun, AConstraintOnAMemberConstrainsItsBits) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct packed { bit [3:0] hi; bit [3:0] lo; } ps_t;\n"
      "class C;\n"
      "  rand ps_t p;\n"
      "  constraint c { p.hi == 4'hA; p.lo inside {[1:3]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  bit [3:0] seen = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (40) begin\n"
      "      if (c.randomize() != 1) bad++;\n"
      "      if (c.p < 8'hA1 || c.p > 8'hA3) bad++;\n"
      "      else seen[c.p.lo] = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, seen);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 14\n");
}

// §18.4: the size of a rand queue may be constrained; the queue is resized at
// its back to the size the constraint gives and every element randomized, so
// five entries become three, each within the range its foreach gives.
TEST(RandQueueRun, AConstrainedSizeResizesTheQueue) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand byte q[$];\n"
      "  constraint s { q.size() == 3; }\n"
      "  constraint v { foreach (q[i]) q[i] inside {[1:9]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok, bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (5) c.q.push_back(42);\n"
      "    ok = c.randomize();\n"
      "    foreach (c.q[i]) if (!(c.q[i] inside {[1:9]})) bad++;\n"
      "    $display(\"%0d %0d %0d\", ok, c.q.size(), bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 3 0\n");
}

// §18.4: a rand queue whose size no constraint names keeps its size, and its
// elements are randomized.
TEST(RandQueueRun, AnUnconstrainedSizeIsKept) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand byte q[$];\n"
      "  constraint v { foreach (q[i]) q[i] inside {[1:9]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok, bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (4) c.q.push_back(42);\n"
      "    ok = c.randomize();\n"
      "    foreach (c.q[i]) if (!(c.q[i] inside {[1:9]})) bad++;\n"
      "    $display(\"%0d %0d %0d\", ok, c.q.size(), bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 0\n");
}

// §18.4: randomize() allocates no class object: grown by its size
// constraint, a rand dynamic array of handles keeps the objects it held,
// their contents randomized, and its elements added are null.
TEST(RandQueueRun, AnArrayOfHandlesKeepsItsObjectsAndAddsNulls) {
  SimFixture f;
  std::string out = RunCapture(
      "class L;\n"
      "  rand bit [7:0] v;\n"
      "  constraint k { v inside {[1:9]}; }\n"
      "endclass\n"
      "class C;\n"
      "  rand L arr[];\n"
      "  constraint s { arr.size == 4; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static L first;\n"
      "    c.arr = new[2];\n"
      "    c.arr[0] = new; c.arr[1] = new;\n"
      "    c.arr[0].v = 200; c.arr[1].v = 200;\n"
      "    first = c.arr[0];\n"
      "    ok = c.randomize();\n"
      "    $display(\"%0d %0d %0d %0d %0d\", ok, c.arr.size(),\n"
      "             c.arr[0] == first && c.arr[1] != null,\n"
      "             c.arr[2] == null && c.arr[3] == null,\n"
      "             c.arr[0].v inside {[1:9]} && c.arr[1].v inside {[1:9]});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 1 1 1\n");
}

// §18.4: a rand unpacked structure has the members its typedef marks rand
// solved with the object's other random variables, and the members it does
// not mark keep their values: addr is drawn from 7 to 9, crc stays 77.
TEST(RandPackedStructRun, ARandUnpackedStructRandomizesItsRandMembers) {
  SimFixture f;
  std::string out = RunCapture(
      "class P;\n"
      "  typedef struct {\n"
      "    rand int addr;\n"
      "    int crc;\n"
      "    rand bit [3:0] tag;\n"
      "  } header;\n"
      "  rand header h1;\n"
      "  constraint c { h1.addr inside {[7:9]}; h1.tag == 4'h5; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    p.h1.crc = 77;\n"
      "    repeat (10) begin\n"
      "      if (p.randomize() != 1) bad++;\n"
      "      if (!(p.h1.addr inside {[7:9]}) || p.h1.tag != 4'h5) bad++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, p.h1.crc);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 77\n");
}

// §18.4: an associative array declared rand has every element randomized,
// its size and its keys left as they are: the two entries written before the
// call are drawn within the range the foreach over their keys gives.
TEST(RandQueueRun, AnAssociativeArrayRandomizesItsElementsKeepingItsKeys) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] m[string];\n"
      "  rand bit [7:0] n[int];\n"
      "  constraint c { foreach (m[k]) m[k] inside {[30:40]};\n"
      "                 foreach (n[k]) n[k] == k + 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.m[\"a\"] = 1; c.m[\"b\"] = 2;\n"
      "    c.n[5] = 0; c.n[9] = 0;\n"
      "    ok = c.randomize();\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", ok, c.m.num(),\n"
      "             c.m.exists(\"a\") && c.m.exists(\"b\"),\n"
      "             c.m[\"a\"] inside {[30:40]} && c.m[\"b\"] inside "
      "{[30:40]},\n"
      "             c.n[5], c.n[9]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 1 1 6 10\n");
}

}  // namespace
