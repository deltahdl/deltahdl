#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SubroutineNameSim,
     ASubroutineDeclaredLaterInItsModuleIsCalledFromAnyScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  int r1, r2, r3, r4, r5;\n"
                 "  wire [31:0] w = later(1);\n"
                 "  initial begin\n"
                 "    r1 = later(4);\n"
                 "    tlater(r2);\n"
                 "    r3 = chain(1);\n"
                 "    begin : blk\n"
                 "      r4 = later(6);\n"
                 "    end\n"
                 "    #2 r5 = w;\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d\",\n"
                 "             r1, r2, r3, r4, r5, g.gr);\n"
                 "  end\n"
                 "  if (1) begin : g\n"
                 "    int gr;\n"
                 "    initial gr = later(7);\n"
                 "  end\n"
                 "  function int chain(int x);\n"
                 "    return later(x) + 100;\n"
                 "  endfunction\n"
                 "  function int later(int x); return x * 11; endfunction\n"
                 "  task tlater(output int y); y = later(2) + 1; endtask\n"
                 "endmodule\n",
                 f),
      "44 23 111 66 11 77\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SubroutineNameSim,
     ASubroutineDeclaredLaterInAPackageUnitInterfaceOrClassIsCalled) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  function int pa(int x); return pb(x) + 1; endfunction\n"
                 "  function int pb(int x); return x * 2; endfunction\n"
                 "endpackage\n"
                 "function int ua(int x); return ub(x) + 3; endfunction\n"
                 "function int ub(int x); return x * 5; endfunction\n"
                 "class K;\n"
                 "  function int a(int x); return b(x) + 1; endfunction\n"
                 "  function int b(int x); return x * 3; endfunction\n"
                 "endclass\n"
                 "interface i;\n"
                 "  int r;\n"
                 "  initial r = ia(2);\n"
                 "  function int ia(int x); return x + 40; endfunction\n"
                 "endinterface\n"
                 "module m;\n"
                 "  class C;\n"
                 "    function int g(int x); return later(x) + 2; "
                 "endfunction\n"
                 "  endclass\n"
                 "  C c = new;\n"
                 "  K k = new;\n"
                 "  i u();\n"
                 "  initial #1 $display(\"%0d %0d %0d %0d %0d\",\n"
                 "      p::pa(3), ua(1), k.a(4), c.g(1), u.r);\n"
                 "  function int later(int x); return x * 11; endfunction\n"
                 "endmodule\n",
                 f),
      "7 8 13 13 42\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SubroutineNameSim, ASubroutineDeclaredLaterInAProgramIsCalled) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program q;\n"
                       "  int r;\n"
                       "  initial begin tq(r); $display(\"%0d\", r); end\n"
                       "  task tq(output int y); y = f2(4); endtask\n"
                       "  function int f2(int x); return x + 5; endfunction\n"
                       "endprogram\n",
                       f),
            "9\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SubroutineNameSim, ASimpleNameNotDeclaredInItsModuleIsSoughtUpward) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module child;\n"
                 "  int r;\n"
                 "  initial r = up(3);\n"
                 "endmodule\n"
                 "module m;\n"
                 "  child c();\n"
                 "  initial #1 $display(\"%0d\", c.r);\n"
                 "  function int up(int x); return x + 1000; endfunction\n"
                 "endmodule\n",
                 f),
      "1003\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
