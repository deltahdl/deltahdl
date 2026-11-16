#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string EachElementCycles(const std::string& decl,
                              const std::string& fill) {
  return "class C;\n"
         "  randc bit [1:0] a" +
         decl +
         ";\n"
         "endclass\n"
         "module t;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    static bit [3:0] seen0 = 0, seen1 = 0;\n"
         "    static int ok = 0;\n" +
         fill +
         "    repeat (4) begin\n"
         "      ok += o.randomize();\n"
         "      seen0[o.a[0]] = 1'b1;\n"
         "      seen1[o.a[1]] = 1'b1;\n"
         "    end\n"
         "    $display(\"%0d %b %b %0d\", ok, seen0, seen1, $size(o.a));\n"
         "  end\n"
         "endmodule\n";
}

TEST(RandcArrayElements, EachElementOfAFixedArrayCycles) {
  SimFixture f;
  EXPECT_EQ(RunCapture(EachElementCycles("[2]", ""), f), "4 1111 1111 2\n");
}

TEST(RandcArrayElements, EachElementOfADynamicArrayCycles) {
  SimFixture f;
  EXPECT_EQ(RunCapture(EachElementCycles("[]", "    o.a = new[2];\n"), f),
            "4 1111 1111 2\n");
}

TEST(RandcArrayElements, EachElementOfAQueueCycles) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(EachElementCycles("[$]", "    o.a = '{2'd0, 2'd0};\n"), f),
      "4 1111 1111 2\n");
}

TEST(RandcArrayElements, EachElementOfAnAssociativeArrayCycles) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          EachElementCycles("[int]", "    o.a[0] = 2'd0; o.a[1] = 2'd0;\n"), f),
      "4 1111 1111 2\n");
}

TEST(RandArrayElements, RandomizeOverwritesEveryElementOfEveryKind) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  rand bit [7:0] a[3];\n"
                       "  rand bit [7:0] d[];\n"
                       "  rand bit [7:0] q[$];\n"
                       "  rand bit [7:0] m[string];\n"
                       "  constraint c {\n"
                       "    foreach (a[i]) a[i] < 100;\n"
                       "    foreach (d[i]) d[i] < 100;\n"
                       "    foreach (q[i]) q[i] < 100;\n"
                       "    foreach (m[k]) m[k] < 100;\n"
                       "  }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    static int ok, kept = 0;\n"
                       "    o.a = '{200, 200, 200};\n"
                       "    o.d = '{200, 200, 200};\n"
                       "    o.q = '{200, 200, 200};\n"
                       "    o.m[\"x\"] = 200; o.m[\"y\"] = 200; "
                       "o.m[\"z\"] = 200;\n"
                       "    ok = o.randomize();\n"
                       "    foreach (o.a[i]) if (o.a[i] == 200) kept++;\n"
                       "    foreach (o.d[i]) if (o.d[i] == 200) kept++;\n"
                       "    foreach (o.q[i]) if (o.q[i] == 200) kept++;\n"
                       "    foreach (o.m[k]) if (o.m[k] == 200) kept++;\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", ok, kept, "
                       "o.d.size(), o.q.size(), o.m.num());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 0 3 3 3\n");
}

constexpr char kEnumMembers[] =
    "typedef enum bit [1:0] {A = 2'b00, B = 2'b11} ab_e;\n"
    "typedef struct packed {\n"
    "  ab_e ValidAB;\n"
    "} VStructEnum;\n"
    "typedef union packed {\n"
    "  ab_e ValidAB;\n"
    "} VUnionEnum;\n";

TEST(EnumMemberOfARandPackedVariable, AUnionMemberReachesUnnamedValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kEnumMembers) +
                           "class C;\n"
                           "  rand VUnionEnum u;\n"
                           "  rand ab_e e;\n"
                           "endclass\n"
                           "module t;\n"
                           "  initial begin\n"
                           "    static C o = new;\n"
                           "    static bit [3:0] su = 0, se = 0;\n"
                           "    repeat (60) begin\n"
                           "      void'(o.randomize());\n"
                           "      su[o.u] = 1'b1;\n"
                           "      se[o.e] = 1'b1;\n"
                           "    end\n"
                           "    $display(\"%b %b\", su, se);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "1111 1001\n");
}

TEST(EnumMemberOfARandPackedVariable, RandcStructAndUnionCycleThroughAllFour) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kEnumMembers) +
                           "class C;\n"
                           "  randc VStructEnum s;\n"
                           "  randc VUnionEnum u;\n"
                           "endclass\n"
                           "module t;\n"
                           "  initial begin\n"
                           "    static C o = new;\n"
                           "    static bit [3:0] ss = 0, su = 0;\n"
                           "    repeat (4) begin\n"
                           "      void'(o.randomize());\n"
                           "      ss[o.s] = 1'b1;\n"
                           "      su[o.u] = 1'b1;\n"
                           "    end\n"
                           "    $display(\"%b %b\", ss, su);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "1111 1111\n");
}

TEST(EnumMemberOfARandPackedVariable, AConstraintNamingAnUnnamedValueIsMet) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kEnumMembers) +
                           "class C;\n"
                           "  rand VStructEnum s;\n"
                           "  rand VUnionEnum u;\n"
                           "  constraint c { s.ValidAB == 2'b10; "
                           "u.ValidAB == 2'b01; }\n"
                           "endclass\n"
                           "module t;\n"
                           "  initial begin\n"
                           "    static C o = new;\n"
                           "    automatic int ok = o.randomize();\n"
                           "    $display(\"%0d %b %b\", ok, o.s, o.u);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "1 10 01\n");
}

TEST(RandPackedStruct, AWholeStructConstraintTreatsItAsIntegral) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct packed {\n"
                       "  bit [3:0] hi;\n"
                       "  bit [3:0] lo;\n"
                       "} s_t;\n"
                       "class C;\n"
                       "  rand s_t s;\n"
                       "  constraint c { s == 8'hA5; }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    automatic int ok = o.randomize();\n"
                       "    $display(\"%0d %h %h\", ok, o.s.hi, o.s.lo);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 a 5\n");
}

TEST(RandUnpackedStruct, ARandcMemberCycles) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class P;\n"
                       "  typedef struct {\n"
                       "    randc bit [1:0] addr;\n"
                       "    int crc;\n"
                       "  } header;\n"
                       "  rand header h1;\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static P p = new;\n"
                       "    static bit [3:0] seen = 0;\n"
                       "    p.h1.crc = 77;\n"
                       "    repeat (4) begin\n"
                       "      void'(p.randomize());\n"
                       "      seen[p.h1.addr] = 1'b1;\n"
                       "    end\n"
                       "    $display(\"%b %0d\", seen, p.h1.crc);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1111 77\n");
}

TEST(RandSizedArray, ADynamicArrayTakesTheSizeOfARandLength) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C;\n"
                 "  rand bit [7:0] len;\n"
                 "  rand integer data[];\n"
                 "  constraint db { data.size == len; len inside "
                 "{[1:12]}; }\n"
                 "endclass\n"
                 "module t;\n"
                 "  initial begin\n"
                 "    static C o = new;\n"
                 "    static int bad = 0;\n"
                 "    static bit [15:0] sizes = 0;\n"
                 "    repeat (40) begin\n"
                 "      if (o.randomize() != 1) bad++;\n"
                 "      if (o.data.size() != o.len) bad++;\n"
                 "      foreach (o.data[i]) if ($isunknown(o.data[i])) "
                 "bad++;\n"
                 "      sizes[o.len] = 1'b1;\n"
                 "    end\n"
                 "    $display(\"%0d %0d\", bad, $countones(sizes) > 1);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0 1\n");
}

TEST(RandSizedArray, ADynamicArrayShrinksAndAQueueGrowsAtTheBack) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  rand bit [7:0] d[];\n"
                       "  rand bit [7:0] q[$];\n"
                       "  constraint c { d.size() == 2; q.size() == 4;\n"
                       "    foreach (d[i]) d[i] inside {[1:9]};\n"
                       "    foreach (q[i]) q[i] inside {[1:9]}; }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    static int ok, bad = 0;\n"
                       "    o.d = '{200, 200, 200, 200, 200};\n"
                       "    o.q = '{200};\n"
                       "    ok = o.randomize();\n"
                       "    foreach (o.d[i]) if (!(o.d[i] inside {[1:9]})) "
                       "bad++;\n"
                       "    foreach (o.q[i]) if (!(o.q[i] inside {[1:9]})) "
                       "bad++;\n"
                       "    $display(\"%0d %0d %0d %0d\", ok, o.d.size(), "
                       "o.q.size(), bad);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 2 4 0\n");
}

TEST(RandSizedArray, DISABLED_AQueueOfHandlesKeepsItsObjectsAndAddsNulls) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class L;\n"
                       "  rand bit [7:0] v;\n"
                       "  constraint k { v inside {[1:9]}; }\n"
                       "endclass\n"
                       "class C;\n"
                       "  rand L q[$];\n"
                       "  constraint s { q.size() == 3; }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    static L first = new, second = new;\n"
                       "    int ok;\n"
                       "    first.v = 200; second.v = 200;\n"
                       "    o.q.push_back(first); o.q.push_back(second);\n"
                       "    ok = o.randomize();\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", ok, o.q.size(),\n"
                       "             o.q[0] == first && o.q[1] == second,\n"
                       "             o.q[2] == null,\n"
                       "             first.v inside {[1:9]} && "
                       "second.v inside {[1:9]});\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 3 1 1 1\n");
}

TEST(RandSizedArray, AShrunkArrayOfHandlesKeepsItsFirstObjects) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class L;\n"
                       "  rand bit [7:0] v;\n"
                       "endclass\n"
                       "class C;\n"
                       "  rand L arr[];\n"
                       "  constraint s { arr.size() == 1; }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    static L first;\n"
                       "    o.arr = new[3];\n"
                       "    foreach (o.arr[i]) o.arr[i] = new;\n"
                       "    first = o.arr[0];\n"
                       "    $display(\"%0d %0d %0d\", o.randomize(), "
                       "o.arr.size(), o.arr[0] == first);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1 1\n");
}

TEST(RandSizedArray, AQueueKeepsTheRandModeOfItsRetainedElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  rand int q[$];\n"
                       "  int n = 3;\n"
                       "  constraint c { q.size() == n; }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    void'(o.randomize());\n"
                       "    o.q[0].rand_mode(0);\n"
                       "    o.q[2].rand_mode(0);\n"
                       "    o.n = 2;\n"
                       "    void'(o.randomize());\n"
                       "    o.n = 3;\n"
                       "    void'(o.randomize());\n"
                       "    $display(\"%0d %0d %0d\", o.q[0].rand_mode(), "
                       "o.q[1].rand_mode(), o.q[2].rand_mode());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 1 1\n");
}

TEST(RandSizedArray, ASizeOrderedBySolveBeforeResizesTheArray) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  rand bit [7:0] a[];\n"
                       "  rand bit [7:0] b;\n"
                       "  constraint c { a.size() inside {[1:4]}; "
                       "b == a.size();\n"
                       "                 solve a.size before b; }\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    static int bad = 0;\n"
                       "    repeat (10) begin\n"
                       "      if (o.randomize() != 1) bad++;\n"
                       "      if (o.b != o.a.size() || o.b < 1 || o.b > 4) "
                       "bad++;\n"
                       "    end\n"
                       "    $display(\"%0d\", bad);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\n");
}

std::string HandlesKept(const std::string& holder, const std::string& fill,
                        const std::string& shown) {
  return "class L;\n"
         "  rand bit [7:0] v;\n"
         "  constraint k { v inside {[1:9]}; }\n"
         "endclass\n" +
         holder +
         "module t;\n"
         "  initial begin\n"
         "    static H o = new;\n"
         "    static L first = new, second = new;\n"
         "    first.v = 200; second.v = 200;\n" +
         fill + "    $display(\"%0d %0d %0d %0d\", o.randomize(), " + shown +
         ",\n"
         "             first.v inside {[1:9]});\n"
         "  end\n"
         "endmodule\n";
}

TEST(RandSizedArray, DISABLED_AShrunkQueueOfHandlesKeepsItsFirstObject) {
  SimFixture f;
  EXPECT_EQ(RunCapture(HandlesKept("class H;\n"
                                   "  rand L q[$];\n"
                                   "  constraint s { q.size() == 1; }\n"
                                   "endclass\n",
                                   "    o.q = '{first, second};\n",
                                   "o.q.size(), o.q[0] == first"),
                       f),
            "1 1 1 1\n");
}

TEST(RandSizedArray, DISABLED_AnUnsizedQueueOfHandlesKeepsItsObjects) {
  SimFixture f;
  EXPECT_EQ(RunCapture(HandlesKept("class H;\n"
                                   "  rand L q[$];\n"
                                   "endclass\n",
                                   "    o.q = '{first, second};\n",
                                   "o.q.size(), o.q[0] == first && "
                                   "o.q[1] == second"),
                       f),
            "1 2 1 1\n");
}

TEST(RandSizedArray, DISABLED_AnAssociativeArrayOfHandlesKeepsItsObjects) {
  SimFixture f;
  EXPECT_EQ(RunCapture(HandlesKept("class H;\n"
                                   "  rand L m[int];\n"
                                   "endclass\n",
                                   "    o.m[3] = first; o.m[7] = second;\n",
                                   "o.m.num(), o.m[3] == first && "
                                   "o.m[7] == second"),
                       f),
            "1 2 1 1\n");
}

TEST(RandSizedArray, AFixedArrayOfHandlesKeepsItsObjects) {
  SimFixture f;
  EXPECT_EQ(RunCapture(HandlesKept("class H;\n"
                                   "  rand L a[2];\n"
                                   "endclass\n",
                                   "    o.a = '{first, second};\n",
                                   "$size(o.a), o.a[0] == first && "
                                   "o.a[1] == second"),
                       f),
            "1 2 1 1\n");
}

}  // namespace
