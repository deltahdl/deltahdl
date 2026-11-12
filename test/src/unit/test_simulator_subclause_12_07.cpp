#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kSumLoops[] = {
    "for (int i = 1; i <= 3; i++) r += i;\n",
    "begin int i; i = 0; repeat (3) begin i++; r += i; end end\n",
    "begin int i; i = 1; while (i <= 3) begin r += i; i++; end end\n",
    "begin int i; i = 1; do begin r += i; i++; end while (i <= 3); end\n",
    ("begin int i; i = 0; forever begin i++; r += i; if (i == 3) break; end "
     "end\n"),
    "begin int a [1:3]; foreach (a[i]) r += i; end\n"};

std::string LoopInEveryProcedure(const std::string& loop) {
  return "package pk;\n"
         "  function automatic int pf();\n"
         "    int r;\n"
         "    r = 0;\n"
         "    " +
         loop +
         "    return r;\n"
         "  endfunction\n"
         "endpackage\n"
         "import pk::*;\n"
         "function automatic int cf();\n"
         "  int r;\n"
         "  r = 0;\n"
         "  " +
         loop +
         "  return r;\n"
         "endfunction\n"
         "class C;\n"
         "  function int m();\n"
         "    int r;\n"
         "    r = 0;\n"
         "    " +
         loop +
         "    return r;\n"
         "  endfunction\n"
         "endclass\n"
         "interface I;\n"
         "  int r;\n"
         "  initial begin\n"
         "    r = 0;\n"
         "    #2 " +
         loop +
         "    $display(\"I %0d\", r);\n"
         "  end\n"
         "endinterface\n"
         "program p;\n"
         "  int r;\n"
         "  initial begin\n"
         "    r = 0;\n"
         "    #3 " +
         loop +
         "    $display(\"P %0d\", r);\n"
         "  end\n"
         "endprogram\n"
         "module t;\n"
         "  I u();\n"
         "  p pp();\n"
         "  function int mf();\n"
         "    int r;\n"
         "    r = 0;\n"
         "    " +
         loop +
         "    return r;\n"
         "  endfunction\n"
         "  task automatic tk(output int r);\n"
         "    r = 0;\n"
         "    " +
         loop +
         "  endtask\n"
         "  if (1) begin : gb\n"
         "    int r;\n"
         "    initial begin\n"
         "      r = 0;\n"
         "      #1 " +
         loop +
         "      $display(\"G %0d\", r);\n"
         "    end\n"
         "  end\n"
         "  initial begin\n"
         "    C c;\n"
         "    int k;\n"
         "    c = new;\n"
         "    tk(k);\n"
         "    $display(\"%0d %0d %0d %0d %0d\", pf(), cf(), c.m(), mf(), k);\n"
         "  end\n"
         "endmodule\n";
}

TEST(LoopStatementSim, EveryKindOfLoopRunsInEveryKindOfProcedure) {
  for (const char* loop : kSumLoops) {
    SimFixture f;
    EXPECT_EQ(RunCapture(LoopInEveryProcedure(loop), f),
              "6 6 6 6 6\nG 6\nI 6\nP 6\n")
        << loop;
    EXPECT_EQ(f.diag.WarningCount(), 0u) << loop;
  }
}

}  // namespace
