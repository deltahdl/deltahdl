#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
         "    static Vars vars = new;\n"
         "    automatic Inner held = vars.in;\n"
         "    static int n = 0, m = 0;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

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

std::string Lone(const std::string& decl, const std::string& constraint) {
  return "class Lone;\n" + decl + constraint +
         "endclass\n"
         "module t;\n"
         "  initial begin\n"
         "    static Lone o = new;\n"
         "    static int n = 0;\n"
         "    repeat (8) if (o.randomize() == 1) n++;\n"
         "    $display(\"%0d\", n);\n"
         "  end\n"
         "endmodule\n";
}

TEST(RandomVariableRun, ALoneRealMemberIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Lone("  rand real r;\n",
                            "  constraint cr { r > 0.0 && r < 2.0; }\n"),
                       f),
            "8\n");
}

TEST(RandomVariableRun, ALoneRandcMemberIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Lone("  randc bit [1:0] c;\n", ""), f), "8\n");
}

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

std::string WithHandle(const std::string& decl, const std::string& constraint) {
  return "class Inner;\n"
         "  rand int v;\n"
         "  constraint cv { v inside {[1:3]}; }\n"
         "endclass\n" +
         Lone("  rand Inner in;\n  rand bit [3:0] w;\n" + decl +
                  "  function new();\n    in = new;\n  endfunction\n",
              "  constraint cw { w > in.v; }\n" + constraint);
}

TEST(RandomVariableRun, ARealBesideARandHandleIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(WithHandle("  rand real r;\n",
                                  "  constraint cr { r > 0.0 && r < 2.0; }\n"),
                       f),
            "8\n");
}

TEST(RandomVariableRun, ARandcBesideARandHandleIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(WithHandle("  randc bit [1:0] c;\n", ""), f), "8\n");
}

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

TEST(RandomVariableRun, ARealBesideARandcIsDrawn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Lone("  rand real r;\n  randc bit [1:0] c;\n",
                            "  constraint cr { r > 0.0 && r < 2.0; }\n"),
                       f),
            "8\n");
}

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

TEST(RandQueueRun, AnArrayOfHandlesWithoutASizeConstraintKeepsItsSize) {
  SimFixture f;
  std::string out = RunCapture(
      "class L;\n"
      "  rand bit [7:0] v;\n"
      "  constraint k { v inside {[1:9]}; }\n"
      "endclass\n"
      "class C;\n"
      "  rand L arr[];\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.arr = new[2];\n"
      "    c.arr[0] = new; c.arr[1] = new;\n"
      "    c.arr[0].v = 200; c.arr[1].v = 200;\n"
      "    $display(\"%0d %0d %0d\", c.randomize(), c.arr.size(),\n"
      "             c.arr[0].v inside {[1:9]} && c.arr[1].v inside {[1:9]});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 1\n");
}

TEST(RandPackedStructRun, AModuleTypedefsRandMembersAreRandomized) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct {\n"
      "  rand int addr;\n"
      "  int crc;\n"
      "  rand bit [3:0] lanes[2];\n"
      "} header;\n"
      "class P;\n"
      "  rand header h1;\n"
      "  constraint c { h1.addr inside {[7:9]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    p.h1.crc = 77;\n"
      "    repeat (10) begin\n"
      "      if (p.randomize() != 1 || !(p.h1.addr inside {[7:9]})) bad++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, p.h1.crc);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 77\n");
}

TEST(RandPackedStructRun, ARandDynamicMemberHasItsElementsRandomized) {
  SimFixture f;
  std::string out = RunCapture(
      "class P;\n"
      "  typedef struct {\n"
      "    rand int addr;\n"
      "    rand byte data[] = {1, 2, 3, 4};\n"
      "  } header;\n"
      "  rand header h1;\n"
      "  constraint c { h1.addr inside {[7:9]};\n"
      "                 foreach (h1.data[i]) h1.data[i] inside {[20:30]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok, bad = 0;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    ok = p.randomize();\n"
      "    foreach (p.h1.data[i]) if (!(p.h1.data[i] inside {[20:30]})) "
      "bad++;\n"
      "    $display(\"%0d %0d %0d %0d\", ok, p.h1.data.size(), bad,\n"
      "             p.h1.addr inside {[7:9]});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 0 1\n");
}

TEST(RandQueueRun, AnAssociativeArrayElementIsNamedByItsWholeIndex) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] m[bit [79:0]];\n"
      "  constraint c { foreach (m[k]) m[k] == (k >> 64) + 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.m[80'h1_0000_0000_0000_0005] = 0; c.m[5] = 0;\n"
      "    ok = c.randomize();\n"
      "    $display(\"%0d %0d %0d %0d\", ok, c.m.num(),\n"
      "             c.m[5], c.m[80'h1_0000_0000_0000_0005]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 1 2\n");
}

TEST(RandQueueRun, AnElementAddedBackByRandomizeIsActive) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int a[];\n"
      "  rand int b;\n"
      "  int n = 3;\n"
      "  constraint c { a.size() == n; foreach (a[i]) a[i] inside {[1:9]};\n"
      "                 b inside {[1:9]}; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    void'(o.randomize());\n"
      "    o.b.rand_mode(0);\n"
      "    o.a[0].rand_mode(0);\n"
      "    o.a[2].rand_mode(0);\n"
      "    o.n = 2;\n"
      "    void'(o.randomize());\n"
      "    o.n = 3;\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d\", o.a[0].rand_mode(), o.a[2].rand_mode(),\n"
      "             o.b.rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 0\n");
}

TEST(RandQueueRun, AnElementAddedBackByNewIsActive) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int a[];\n"
      "  static rand int s[];\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.a = new[3];\n"
      "    o.s = new[3];\n"
      "    o.a[0].rand_mode(0);\n"
      "    o.a[2].rand_mode(0);\n"
      "    o.s[2].rand_mode(0);\n"
      "    o.a = new[2];\n"
      "    o.s = new[2];\n"
      "    o.a = new[3];\n"
      "    o.s = new[3];\n"
      "    $display(\"%0d %0d %0d\", o.a[0].rand_mode(), o.a[2].rand_mode(),\n"
      "             o.s[2].rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 1\n");
}

TEST(RandQueueRun, AKeptSoftSizeConstraintResizesTheArray) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] a[];\n"
      "  constraint c { soft a.size() == 6; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.a = new[2];\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d\", o.a.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6\n");
}

TEST(RandQueueRun, AnInlineSizeConstraintResizesTheArray) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] a[];\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    void'(o.randomize() with { a.size() == 4; });\n"
      "    $write(\"%0d \", o.a.size());\n"
      "    void'(o.randomize() with { soft a.size() == 5; });\n"
      "    $write(\"%0d \", o.a.size());\n"
      "    void'(o.randomize() with { a[0] == 3; });\n"
      "    $display(\"%0d %0d\", o.a.size(), o.a[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 5 5 3\n");
}

TEST(RandQueueRun, DisableSoftOnTheSizeLeavesTheArrayItsSize) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] a[];\n"
      "  rand bit [3:0] b[];\n"
      "  rand bit [3:0] x;\n"
      "  constraint c1 { soft a.size() == 6; soft b.size() == 5; soft x == 1; "
      "}\n"
      "  constraint c2 { disable soft a.size(); disable soft b.size;\n"
      "                  disable soft x; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.a = new[2];\n"
      "    o.b = new[3];\n"
      "    void'(o.randomize());\n"
      "    $write(\"%0d %0d \", o.a.size(), o.b.size());\n"
      "    void'(o.randomize() with { soft a.size() == 4; });\n"
      "    $display(\"%0d\", o.a.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 3 4\n");
}

}  // namespace
