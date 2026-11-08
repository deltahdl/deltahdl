#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlRun, StatusNameOfAChainedCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  process c;\n"
                       "  initial begin\n"
                       "    fork begin c = process::self(); #1; end join_none\n"
                       "    #0 $display(\"%s\", c.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "WAITING\n");
}

TEST(FineGrainProcessControlRun, StatusNameThroughAnArrayElement) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  process job[2];\n"
                 "  initial begin\n"
                 "    fork begin job[1] = process::self(); #1; end join_none\n"
                 "    #0 $display(\"%s\", job[1].status().name());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "WAITING\n");
}

TEST(FineGrainProcessControlRun, StatusNameOfAPropertyInAClassFunction) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class Worker;\n"
                 "  process p, q;\n"
                 "  task start;\n"
                 "    fork\n"
                 "      begin p = process::self(); #10; end\n"
                 "      begin q = process::self(); #5; end\n"
                 "    join_none\n"
                 "    #0;\n"
                 "  endtask\n"
                 "  function string st; return p.status().name(); endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  Worker w = new;\n"
                 "  initial begin\n"
                 "    w.start();\n"
                 "    $display(\"st %s\", w.st());\n"
                 "    #6 $display(\"q %s\", w.q.status().name());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "st WAITING\n"
      "q FINISHED\n");
}

TEST(FineGrainProcessControlRun, AwaitAndKillThroughArrayElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  process arr[2]; int fin;\n"
                       "  initial begin\n"
                       "    fork begin arr[0] = process::self(); #5 fin += 10; "
                       "end join_none\n"
                       "    wait (arr[0] != null);\n"
                       "    arr[0].await();\n"
                       "    $display(\"await @%0d fin=%0d\", $time, fin);\n"
                       "    fork begin arr[1] = process::self(); #5 fin += "
                       "100; end join_none\n"
                       "    wait (arr[1] != null);\n"
                       "    arr[1].kill();\n"
                       "    #10 $display(\"kill @%0d fin=%0d\", $time, fin);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "await @5 fin=10\n"
            "kill @15 fin=10\n");
}

TEST(FineGrainProcessControlRun, ClauseExampleJobArrayInAClassTask) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "class Runner;\n"
          "  process job[]; int fin;\n"
          "  task do_n_way(int N);\n"
          "    job = new[N];\n"
          "    foreach (job[j])\n"
          "      fork\n"
          "        automatic int k = j;\n"
          "        begin job[k] = process::self(); #(2 + 4 * k) fin += 1; end\n"
          "      join_none\n"
          "    foreach (job[j]) wait (job[j] != null);\n"
          "    job[0].await();\n"
          "    $display(\"first done @%0d\", $time);\n"
          "    foreach (job[j]) if (job[j].status != process::FINISHED) "
          "job[j].kill();\n"
          "    $display(\"j1 %s j2 %s\", job[1].status().name(), "
          "job[2].status().name());\n"
          "  endtask\n"
          "endclass\n"
          "module t;\n"
          "  Runner r = new;\n"
          "  initial begin r.do_n_way(3); #7 $display(\"end @%0d fin=%0d\", "
          "$time, r.fin); end\n"
          "endmodule\n",
          f),
      "first done @2\n"
      "j1 KILLED j2 KILLED\n"
      "end @9 fin=1\n");
}

TEST(FineGrainProcessControlRun, MethodsWrittenWithoutAnArgumentList) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  process p, q; int x;\n"
          "  initial begin\n"
          "    fork begin p = process::self(); #5 x = 1; end join_none\n"
          "    fork begin q = process::self(); #5 x += 10; end join_none\n"
          "    #1 $display(\"st=%0d\", p.status);\n"
          "    p.kill;\n"
          "    q.suspend;\n"
          "    #10 $display(\"x=%0d p=%0d q=%0d\", x, p.status == "
          "process::KILLED,\n"
          "                 q.status == process::SUSPENDED);\n"
          "  end\n"
          "endmodule\n",
          f),
      "st=2\n"
      "x=0 p=1 q=1\n");
}

TEST(FineGrainProcessControlRun, AwaitWrittenWithoutAnArgumentList) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  process p; int x;\n"
                 "  initial begin\n"
                 "    fork begin p = process::self(); #5 x = 1; end join_none\n"
                 "    #1 p.await;\n"
                 "    $display(\"await @%0d x=%0d\", $time, x);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "await @5 x=1\n");
}

TEST(FineGrainProcessControlRun, InitialProcessThatEndsIsFinished) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  process b, c; event e;\n"
                       "  initial begin b = process::self(); @e; end\n"
                       "  initial begin c = process::self(); #2; end\n"
                       "  initial begin\n"
                       "    #1 -> e;\n"
                       "    #3 $display(\"b=%s c=%s\", b.status().name(), "
                       "c.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "b=FINISHED c=FINISHED\n");
}

TEST(FineGrainProcessControlRun, AwaitOnAnInitialProcessReturnsAtItsEnd) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  process b;\n"
                       "  initial begin b = process::self(); #2; end\n"
                       "  initial begin #1 b.await(); $display(\"awaited "
                       "@%0d\", $time); end\n"
                       "endmodule\n",
                       f),
            "awaited @2\n");
}

TEST(FineGrainProcessControlRun, ProcessSuspendingItselfStopsUntilResumed) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  process a;\n"
                 "  initial begin\n"
                 "    a = process::self();\n"
                 "    a.suspend();\n"
                 "    $display(\"a back @%0d\", $time);\n"
                 "  end\n"
                 "  initial begin\n"
                 "    #0 $display(\"a %s @%0d\", a.status().name(), $time);\n"
                 "    #2 a.resume();\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "a SUSPENDED @0\n"
      "a back @2\n");
}

TEST(FineGrainProcessControlRun, ResumeAfterAndBeforeASuspendedDelayExpires) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  process a, b;\n"
                 "  initial begin a = process::self(); #10; $display(\"a woke "
                 "@%0d\", $time); end\n"
                 "  initial begin b = process::self(); #10; $display(\"b woke "
                 "@%0d\", $time); end\n"
                 "  initial begin\n"
                 "    #3 a.suspend(); b.suspend();\n"
                 "    $display(\"a %s @%0d\", a.status().name(), $time);\n"
                 "    #2 b.resume();\n"
                 "    #10 a.resume();\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "a SUSPENDED @3\n"
      "b woke @10\n"
      "a woke @15\n");
}

TEST(FineGrainProcessControlRun,
     SuspendedEventWaitMissesTheTriggerAndWaitsForTheNext) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  process b; event e;\n"
                       "  initial begin b = process::self(); @e; $display(\"b "
                       "back @%0d\", $time); end\n"
                       "  initial begin\n"
                       "    #1 b.suspend();\n"
                       "    #1 -> e;\n"
                       "    #2 b.resume();\n"
                       "    #3 -> e;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "b back @7\n");
}

TEST(FineGrainProcessControlRun, StatusNameOfAModuleStateVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  process c;\n"
                       "  process::state ms;\n"
                       "  initial begin\n"
                       "    fork begin c = process::self(); #1; end join_none\n"
                       "    #0 ms = c.status();\n"
                       "    $display(\"%s\", ms.name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "WAITING\n");
}

TEST(FineGrainProcessControlRun, AProcessDisableForkEndsIsKilled) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; process p;\n"
                 "  initial begin\n"
                 "    fork begin p = process::self(); #100; end join_none\n"
                 "    #1 disable fork;\n"
                 "    $display(\"%s\", p.status().name());\n"
                 "    p.await();\n"
                 "    $display(\"after %0t\", $time);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "KILLED\nafter 1\n");
}

TEST(FineGrainProcessControlRun, KillReachesAndReleasesEveryDescendant) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; int x; process p, c;\n"
                 "  initial begin\n"
                 "    x = 0;\n"
                 "    fork begin\n"
                 "      p = process::self();\n"
                 "      fork begin fork #10 x = 99; join_none end join_none\n"
                 "      fork begin c = process::self(); #100; end join_none\n"
                 "      #100;\n"
                 "    end join_none\n"
                 "    #1 fork begin c.await(); $display(\"c %0t\", $time); end "
                 "join_none\n"
                 "    #1 p.kill();\n"
                 "    #1 p.kill();\n"
                 "    #20 $display(\"x=%0d\", x);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "c 2\nx=0\n");
}

TEST(FineGrainProcessControlRun, SuspendDesensitizesAWaitCondition) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; bit go, go2; process p, q;\n"
                       "  initial begin\n"
                       "    p = process::self(); wait (go);\n"
                       "    $display(\"p %0t\", $time);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    q = process::self(); wait (go2);\n"
                       "    $display(\"q %0t\", $time);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 p.suspend(); q.suspend();\n"
                       "    #1 go = 1; go2 = 1;\n"
                       "    #1 go2 = 0;\n"
                       "    #9 p.resume(); q.resume();\n"
                       "    #3 go2 = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "p 12\nq 15\n");
}

TEST(FineGrainProcessControlRun,
     AResumedProgramProcessRunsInTheReactiveRegion) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p; process h; int r;\n"
                       "  initial begin\n"
                       "    h = process::self(); h.suspend();\n"
                       "    $display(\"r=%0d\", r);\n"
                       "  end\n"
                       "  initial begin #1; h.resume(); r <= 1; end\n"
                       "endprogram\n",
                       f),
            "r=0\n");
}

TEST(FineGrainProcessControlRun, SrandomCalledOnSelfReseedsTheCallingProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; process p; int a, b;\n"
                       "  initial begin\n"
                       "    process::self().srandom(5); a = $urandom;\n"
                       "    p = process::self(); p.srandom(5); b = $urandom;\n"
                       "    $display(\"%0d\", a == b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlRun, StatusCalledOnSelfIsRunning) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial $display(\"%s\", "
                       "process::self().status().name());\n"
                       "endmodule\n",
                       f),
            "RUNNING\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlRun,
     SrandomCalledOnAFunctionsResultReseedsItsProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; int a, b;\n"
                       "  function automatic process me();\n"
                       "    return process::self();\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    me().srandom(5); a = $urandom;\n"
                       "    process::self().srandom(5); b = $urandom;\n"
                       "    $display(\"%0d\", a == b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlRun, StatusCalledOnAMethodsResultIsRunning) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class W;\n"
                       "  function std::process mine();\n"
                       "    return process::self();\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t; W w;\n"
                       "  initial begin\n"
                       "    w = new;\n"
                       "    $display(\"%s\", w.mine().status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "RUNNING\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlRun,
     SrandomCalledThroughAStructureMemberReseedsItsProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct { process p; int n; } holder_t;\n"
                       "  holder_t s;\n"
                       "  process q;\n"
                       "  int a, b;\n"
                       "  initial begin\n"
                       "    fork q = process::self(); join\n"
                       "    s.p = process::self();\n"
                       "    s.p.srandom(5); a = $urandom;\n"
                       "    process::self().srandom(5); b = $urandom;\n"
                       "    $display(\"%0d\", a == b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlRun, StatusCalledThroughAStructureMemberIsRunning) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  struct { int n; std::process p; } s;\n"
                       "  initial begin\n"
                       "    s.p = process::self();\n"
                       "    $display(\"%s\", s.p.status().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "RUNNING\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
