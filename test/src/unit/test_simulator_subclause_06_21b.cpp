#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(LifetimeSim, CompilationUnitVariableIsOneStaticSharedByModules) {
  SimFixture f;
  EXPECT_EQ(RunCapture("int g;\n"
                       "module a;\n"
                       "  initial g = 5;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  a u();\n"
                       "  initial #1 $display(\"%0d\", g);\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(LifetimeSim, InterfaceAndProgramVariablesOutliveTheProcessWritingThem) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  int v;\n"
                       "  initial v = 3;\n"
                       "  initial #1 $display(\"i %0d\", v);\n"
                       "endinterface\n"
                       "program prg;\n"
                       "  int v;\n"
                       "  initial v = 4;\n"
                       "  initial #2 $display(\"p %0d\", v);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  ifc i();\n"
                       "  prg p();\n"
                       "endmodule\n",
                       f),
            "i 3\np 4\n");
}

TEST(LifetimeSim, TaskLocalsTakeTheTasksLifetimeUnlessStatedOtherwise) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  task st(output int r, output int a);\n"
                       "    int c;\n"
                       "    automatic int x = 0;\n"
                       "    c++;\n"
                       "    x++;\n"
                       "    r = c;\n"
                       "    a = x;\n"
                       "  endtask\n"
                       "  task automatic at(output int r, output int a);\n"
                       "    int c;\n"
                       "    static int s;\n"
                       "    c++;\n"
                       "    s++;\n"
                       "    r = c;\n"
                       "    a = s;\n"
                       "  endtask\n"
                       "  int r, a;\n"
                       "  initial begin\n"
                       "    st(r, a);\n"
                       "    st(r, a);\n"
                       "    $display(\"st %0d %0d\", r, a);\n"
                       "    at(r, a);\n"
                       "    at(r, a);\n"
                       "    $display(\"at %0d %0d\", r, a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "st 2 1\nat 1 2\n");
}

TEST(LifetimeSim, ForkSpawnedByAnAutomaticTaskKeepsItsLocalsAlive) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  task automatic t(int v);\n"
                       "    int x;\n"
                       "    x = v;\n"
                       "    fork\n"
                       "      #2 $display(\"x %0d\", x);\n"
                       "    join_none\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    t(5);\n"
                       "    t(7);\n"
                       "    $display(\"returned\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "returned\nx 5\nx 7\n");
}

TEST(LifetimeSim, HierarchicalReferenceAboveTheDeclarationReachesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  initial top.v = 1;\n"
                       "  int v;\n"
                       "  initial #1 $display(\"%0d\", v);\n"
                       "endmodule\n",
                       f),
            "1\n");
}

struct AutomaticScope {
  std::string_view name;
  std::string_view before_block;
  std::string_view after_block;
};

constexpr AutomaticScope kAutomaticScopes[] = {
    {"module", "module automatic top;\n", "endmodule\n"},
    {"generate block", "module automatic top;\n  if (1) begin : g\n",
     "  end\nendmodule\n"},
    {"interface", "interface automatic ifc;\n",
     "endinterface\nmodule top;\n  ifc i();\nendmodule\n"},
    {"program", "program automatic prg;\n",
     "endprogram\nmodule top;\n  prg p();\nendmodule\n"},
};

TEST(LifetimeSim, DISABLED_AutomaticScopesBlockLocalIsInitializedOnEachEntry) {
  for (const auto& scope : kAutomaticScopes) {
    SCOPED_TRACE(scope.name);
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string(scope.before_block) +
                             "  initial begin\n"
                             "    for (int k = 0; k < 3; k++) begin\n"
                             "      int n = 0;\n"
                             "      n++;\n"
                             "      $write(\"%0d\", n);\n"
                             "    end\n"
                             "    $display;\n"
                             "  end\n" +
                             std::string(scope.after_block),
                         f),
              "111\n");
  }
}

TEST(LifetimeSim, AutomaticModuleKeepsItsOwnVariablesAndStaticTasksStatic) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module automatic top;\n"
                       "  int i;\n"
                       "  task bump;\n"
                       "    i++;\n"
                       "  endtask\n"
                       "  task static sc(output int r);\n"
                       "    int c;\n"
                       "    c++;\n"
                       "    r = c;\n"
                       "  endtask\n"
                       "  task ac(output int r);\n"
                       "    static int c;\n"
                       "    c++;\n"
                       "    r = c;\n"
                       "  endtask\n"
                       "  int r, s;\n"
                       "  initial begin\n"
                       "    bump();\n"
                       "    bump();\n"
                       "    sc(r);\n"
                       "    sc(r);\n"
                       "    ac(s);\n"
                       "    ac(s);\n"
                       "    $display(\"%0d %0d %0d\", i, r, s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 2 2\n");
}

TEST(LifetimeSim, AutomaticPackageInterfaceAndProgramSubroutinesStartAfresh) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package automatic p;\n"
                       "  function int f;\n"
                       "    int c;\n"
                       "    c++;\n"
                       "    return c;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "interface automatic ifc;\n"
                       "  function int g;\n"
                       "    int c;\n"
                       "    c++;\n"
                       "    return c;\n"
                       "  endfunction\n"
                       "endinterface\n"
                       "program automatic prg;\n"
                       "  function int h;\n"
                       "    int c;\n"
                       "    c++;\n"
                       "    return c;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    void'(h());\n"
                       "    #1 $display(\"p %0d\", h());\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  ifc i();\n"
                       "  prg q();\n"
                       "  initial begin\n"
                       "    void'(p::f());\n"
                       "    void'(i.g());\n"
                       "    $display(\"%0d %0d\", p::f(), i.g());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1\np 1\n");
}

TEST(LifetimeSim, ClassMethodLocalStartsAfreshOnEachCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  function int f;\n"
                       "    int c;\n"
                       "    c++;\n"
                       "    return c;\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module top;\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    void'(h.f());\n"
                       "    $display(\"%0d\", h.f());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(LifetimeSim, NonblockingWriteOfANonStaticPropertyLands) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  int v;\n"
                       "endclass\n"
                       "module top;\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    h.v <= 6;\n"
                       "    $display(\"%0d\", h.v);\n"
                       "    #1 $display(\"%0d\", h.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\n6\n");
}

TEST(LifetimeSim, StaticSubroutineLocalsAreReachedByPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  task t;\n"
                       "    int x;\n"
                       "    x++;\n"
                       "  endtask\n"
                       "endmodule\n"
                       "module top;\n"
                       "  task t;\n"
                       "    int x;\n"
                       "    x = x + 1;\n"
                       "  endtask\n"
                       "  task automatic ta;\n"
                       "    static int s;\n"
                       "    int a;\n"
                       "    s++;\n"
                       "  endtask\n"
                       "  function int f;\n"
                       "    int v;\n"
                       "    v = 9;\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "  task tb;\n"
                       "    begin : blk\n"
                       "      static int y;\n"
                       "      y = 4;\n"
                       "    end\n"
                       "  endtask\n"
                       "  sub u();\n"
                       "  initial begin\n"
                       "    t();\n"
                       "    t();\n"
                       "    ta();\n"
                       "    ta();\n"
                       "    void'(f());\n"
                       "    tb();\n"
                       "    u.t();\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", t.x, ta.s, f.v, "
                       "tb.blk.y, top.u.t.x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 2 9 4 1\n");
}

std::string TaskLocalWrittenThroughAPath(std::string_view calls_before) {
  return std::string(
             "module top;\n"
             "  task t(output int r);\n"
             "    int x;\n"
             "    x = x + 1;\n"
             "    r = x;\n"
             "  endtask\n"
             "  int r;\n"
             "  initial begin\n") +
         std::string(calls_before) +
         "    t.x = 5;\n"
         "    t(r);\n"
         "    $display(\"%0d\", r);\n"
         "  end\n"
         "endmodule\n";
}

TEST(LifetimeSim, WriteThroughAPathAfterACallIsSeenByTheNextCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture(TaskLocalWrittenThroughAPath("    t(r);\n"), f), "6\n");
}

TEST(LifetimeSim, DISABLED_WriteThroughAPathBeforeTheFirstCallIsKept) {
  SimFixture f;
  EXPECT_EQ(RunCapture(TaskLocalWrittenThroughAPath(""), f), "6\n");
}

TEST(LifetimeSim, NamedBlocksStaticIsReachedBesideAnUnnamedBlocksTwin) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  initial begin\n"
                       "    begin\n"
                       "      static int x = 1;\n"
                       "    end\n"
                       "    begin : nb\n"
                       "      static int x = 2;\n"
                       "    end\n"
                       "  end\n"
                       "  initial #1 $display(\"%0d\", nb.x);\n"
                       "endmodule\n",
                       f),
            "2\n");
}

}  // namespace
