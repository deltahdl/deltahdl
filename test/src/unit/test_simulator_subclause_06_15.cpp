#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ClassDataType, AClassVariableHoldsAHandleInEveryPlaceItIsDeclared) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "class C;\n  int v;\n  C next;\n"
          "  function new(int x);\n    v = x;\n  endfunction\nendclass\n"
          "package k;\n  class P;\n    int v = 7;\n  endclass\n"
          "  P p = new;\nendpackage\n"
          "C uc = new(2);\n"
          "interface ifc;\n  C c = new(3);\nendinterface\n"
          "program pg;\n  C c;\n  initial begin\n    c = new(4);\n"
          "    $display(\"program %0d\", c.v);\n  end\nendprogram\n"
          "module t;\n  typedef struct { C c; } S;\n  C m = new(1);\n"
          "  C arr[2];\n  C q[$];\n  C aa[int];\n  S s;\n  ifc i();\n"
          "  pg u();\n  if (1) begin : g\n    C c = new(5);\n  end\n"
          "  function automatic C make(int x);\n    C l = new(x);\n"
          "    return l;\n  endfunction\n"
          "  function int kept();\n    static C sl = new(14);\n"
          "    return sl.v;\n  endfunction\n"
          "  task automatic give(output C o);\n    o = new(9);\n  endtask\n"
          "  C o;\n"
          "  initial begin\n"
          "    arr[1] = new(6);\n    o = new(8);\n    q.push_back(o);\n"
          "    aa[3] = new(10);\n    s.c = new(11);\n    m.next = new(12);\n"
          "    give(o);\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d "
          "%0d\", m.v, uc.v, i.c.v, k::p.v, g.c.v, arr[1].v, q[0].v, "
          "aa[3].v, s.c.v, m.next.v, make(13).v, o.v, kept());\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 2 3 7 5 6 8 10 11 12 13 9 14\nprogram 4\n");
}

TEST(ClassDataType, CopiesOfAHandleNameOneObjectAndNullNamesNone) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n  int v;\nendclass\n"
                       "module t;\n  C a, b, n;\n"
                       "  initial begin\n    a = new;\n    b = a;\n"
                       "    b.v = 40;\n    n = new;\n"
                       "    $display(\"%0d %0d %0d %0d\", a.v, a == b, a == n, "
                       "n.v);\n"
                       "    b = null;\n"
                       "    $display(\"%0d %0d\", b == null, a.v);\n"
                       "  end\nendmodule\n",
                       f),
            "40 1 0 0\n1 40\n");
}

}  // namespace
