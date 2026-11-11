#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlHandles,
     SelfGivesOneHandlePerProcessAndDistinctOnesAcross) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process a, b, c;\n"
                       "  initial begin\n"
                       "    a = process::self(); b = process::self();\n"
                       "    fork c = process::self(); join\n"
                       "    $display(\"%0d %0d\", a == b, a == c);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlHandles,
     DISABLED_AHandleHeldInAPackageControlsItsProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk; process gp; endpackage\n"
                       "module t; int x;\n"
                       "  initial begin\n"
                       "    fork begin pk::gp = process::self(); #5 x = 1; end "
                       "join_none\n"
                       "    #1 pk::gp.kill();\n"
                       "    #9 $display(\"x=%0d %s\", x, "
                       "pk::gp.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "x=0 KILLED\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlHandles,
     DISABLED_AHandleHeldInAnInterfaceControlsItsProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; process ip; endinterface\n"
                       "module t; ifc i(); int x;\n"
                       "  initial begin\n"
                       "    fork begin i.ip = process::self(); #5 x = 1; end "
                       "join_none\n"
                       "    #1 i.ip.await();\n"
                       "    $display(\"%0t x=%0d %s\", $time, x, "
                       "i.ip.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5 x=1 FINISHED\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlStatus, StatusIsWaitingInEveryBlockingStatement) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; process pe, pw, pj, pa; event e; bit go;\n"
                 "  initial begin\n"
                 "    fork begin pe = process::self(); @e; end join_none\n"
                 "    fork begin pw = process::self(); wait (go); end "
                 "join_none\n"
                 "    fork begin pj = process::self(); fork #9; join end "
                 "join_none\n"
                 "    fork begin pa = process::self(); #1 pj.await(); end "
                 "join_none\n"
                 "    #2 $display(\"%s %s %s %s\", pe.status().name(),\n"
                 "                pw.status().name(), pj.status().name(),\n"
                 "                pa.status().name());\n"
                 "    -> e; go = 1;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "WAITING WAITING WAITING WAITING\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlStatus, DisablingANamedForkLeavesItsProcessKilled) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process p; int x;\n"
                       "  initial begin\n"
                       "    fork : f\n"
                       "      begin p = process::self(); #5 x = 1; end\n"
                       "    join_none\n"
                       "    #1 disable f;\n"
                       "    #10 $display(\"%s x=%0d\", p.status().name(), x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "KILLED x=0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlKill, AProcessKillingItselfStopsAtTheCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process p; int x;\n"
                       "  initial begin\n"
                       "    fork begin p = process::self(); x = 1; p.kill(); "
                       "x = 2; end join_none\n"
                       "    #1 $display(\"x=%0d %s\", x, p.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "x=1 KILLED\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlKill, KillingASuspendedProcessLeavesItKilled) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process p; int x;\n"
                       "  initial begin\n"
                       "    fork begin p = process::self(); #5 x = 1; end "
                       "join_none\n"
                       "    #1 p.suspend(); p.kill(); p.resume();\n"
                       "    #10 $display(\"x=%0d %s\", x, p.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "x=0 KILLED\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlAwait, AwaitOnAnEndedProcessReturnsAtOnce) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process p, q;\n"
                       "  initial begin\n"
                       "    fork begin p = process::self(); #1; end join_none\n"
                       "    fork begin q = process::self(); #9; end join_none\n"
                       "    #2 q.kill();\n"
                       "    #1 p.await(); q.await();\n"
                       "    $display(\"%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlSuspend, AFunctionMaySuspendAnotherProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process p; int x;\n"
                       "  function void stop(process h); h.suspend(); "
                       "endfunction\n"
                       "  initial begin\n"
                       "    fork begin p = process::self(); #5 x = 1; end "
                       "join_none\n"
                       "    #1 stop(p);\n"
                       "    #10 $display(\"x=%0d %s\", x, p.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "x=0 SUSPENDED\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlSuspend,
     APackageFunctionSuspendingItsOwnProcessIsAnError) {
  SimFixture f;
  RunCapture(
      "package pk;\n"
      "  function void halt(); process::self().suspend(); endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  initial pk::halt();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot suspend its own execution", 2,
                            "9.7"));
}

TEST(FineGrainProcessControlSuspend,
     DISABLED_AClassFunctionSuspendingItsOwnProcessIsAnError) {
  SimFixture f;
  RunCapture(
      "class C;\n"
      "  function void halt();\n"
      "    process::self().suspend();\n"
      "  endfunction\n"
      "endclass\n"
      "module t; C c = new;\n"
      "  initial c.halt();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot suspend its own execution", 3,
                            "9.7"));
}

TEST(FineGrainProcessControlResume, ResumeOnAnEndedProcessHasNoEffect) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process p, q;\n"
                       "  initial begin\n"
                       "    fork begin p = process::self(); end join_none\n"
                       "    fork begin q = process::self(); #9; end join_none\n"
                       "    #1 q.kill(); p.resume(); q.resume();\n"
                       "    $display(\"%s %s\", p.status().name(), "
                       "q.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "FINISHED KILLED\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlResume,
     AResumedModuleProcessRunsInTheActiveRegion) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process h; int r;\n"
                       "  initial begin\n"
                       "    h = process::self(); h.suspend();\n"
                       "    $display(\"r=%0d @%0t\", r, $time);\n"
                       "  end\n"
                       "  initial begin #1 h.resume(); r <= 1; end\n"
                       "endmodule\n",
                       f),
            "r=0 @1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlRestriction,
     AnAlwaysProcessAndItsForkAreSuspendedResumedAndKilled) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process a, k; int n, m; bit clk;\n"
                       "  always begin a = process::self(); #2 n++; end\n"
                       "  always @(posedge clk) fork begin k = "
                       "process::self(); #3 m++; end join_none\n"
                       "  initial begin\n"
                       "    #0 clk = 1;\n"
                       "    #3 a.suspend();\n"
                       "    #5 a.resume(); k.await();\n"
                       "    #1 a.kill();\n"
                       "    #5 $display(\"n=%0d m=%0d %s\", n, m, "
                       "a.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=2 m=1 KILLED\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlRestriction,
     KillOnAContinuousAssignmentProcessIsAnError) {
  SimFixture f;
  RunCapture(
      "module t; logic a, y;\n"
      "  function automatic logic f(logic v);\n"
      "    process::self().kill();\n"
      "    return v;\n"
      "  endfunction\n"
      "  assign y = f(a);\n"
      "  initial #1 a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "kill() acts only on a process", 3, "9.7"));
}

}  // namespace
