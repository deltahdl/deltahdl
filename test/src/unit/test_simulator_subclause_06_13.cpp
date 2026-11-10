#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(VoidDataType, VoidFunctionCalledAsAStatementRunsInEveryPlace) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package k;\n  int n;\n  function void f();\n"
                 "    n = 1;\n  endfunction\nendpackage\n"
                 "int un;\nfunction void uf();\n  un = 2;\nendfunction\n"
                 "interface ifc;\n  int n;\n  function void f();\n"
                 "    n = 3;\n  endfunction\nendinterface\n"
                 "class C;\n  int n;\n  function void f();\n"
                 "    n = 4;\n  endfunction\n"
                 "  static int s;\n  static function void sf();\n"
                 "    s = 5;\n  endfunction\nendclass\n"
                 "module t;\n  int n, o;\n  ifc i();\n  C c = new;\n"
                 "  function void f();\n    n = 6;\n  endfunction\n"
                 "  function automatic void fa(output int x);\n"
                 "    x = 7;\n    return;\n    x = 0;\n  endfunction\n"
                 "  if (1) begin : g\n    int m;\n"
                 "    function void gf();\n      m = 8;\n"
                 "    endfunction\n  end\n"
                 "  initial begin\n"
                 "    k::f();\n    uf();\n    i.f();\n    c.f();\n"
                 "    C::sf();\n    f();\n    fa(o);\n    g.gf();\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", k::n, "
                 "un, i.n, c.n, C::s, n, o, g.m);\n"
                 "  end\nendmodule\n",
                 f),
      "1 2 3 4 5 6 7 8\n");
}

TEST(VoidDataType, VoidMemberOfATaggedUnionHoldsItsTagInEveryPlace) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package k;\n"
                 "  typedef union tagged { void N; int V; } T;\n"
                 "endpackage\n"
                 "typedef union tagged { void N; byte V; } UT;\n"
                 "class C;\n  UT p;\n"
                 "  function int m();\n"
                 "    return p matches tagged N ? 1 : 0;\n"
                 "  endfunction\nendclass\n"
                 "interface ifc;\n  UT u = tagged N;\n  int r;\n"
                 "  initial r = u matches tagged N ? 1 : 0;\n"
                 "endinterface\n"
                 "module t;\n"
                 "  k::T a = tagged N;\n  UT b;\n  C c = new;\n  ifc i();\n"
                 "  union tagged { void N; int V; } d = tagged V 5;\n"
                 "  function automatic int f();\n"
                 "    k::T l = tagged N;\n"
                 "    return l matches tagged N ? 1 : 0;\n"
                 "  endfunction\n"
                 "  function automatic int h();\n"
                 "    union tagged { void N; int V; } l;\n"
                 "    l = tagged N;\n"
                 "    return l matches tagged N ? 1 : 0;\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    b = tagged N;\n    c.p = tagged N;\n    d = tagged N;\n"
                 "    #1;\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", "
                 "a matches tagged N ? 1 : 0, b matches tagged N ? 1 : 0, "
                 "c.p matches tagged N ? 1 : 0, c.m(), i.r, "
                 "d matches tagged N ? 1 : 0, f(), h());\n"
                 "    b = tagged V 3;\n"
                 "    $display(\"%0d\", b matches tagged N ? 1 : 0);\n"
                 "  end\nendmodule\n",
                 f),
      "1 1 1 1 1 1 1 1\n0\n");
}

}  // namespace
