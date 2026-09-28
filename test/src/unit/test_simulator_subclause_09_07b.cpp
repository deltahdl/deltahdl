#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §9.7 with §6.19.5.6: status() answers a value of the enumeration
// process::state, so name() chained on the call is the member's name.
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

// §9.7: the handle status() is called through may be an element of an array
// of them, as §9.7's own example keeps them.
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

// §9.7 with §8.6: a process handle held as a property is read by its bare name
// in a method, and through another handle, `w.q`, from outside.
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

// §9.7: await() and kill() act on the process the handle refers to, wherever
// the handle is held; through an element of an array, await() waits for the
// process to end and kill() ends it.
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

// §9.7's own do_n_way pattern in a class task: the forked processes' handles
// held in a dynamic array property, the first awaited and the rest killed, the
// status read without an argument list as the example writes it.
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

// §9.7 with A.8.2: a method call's argument list may be omitted, so `p.kill;`
// kills, `q.suspend;` suspends and `p.status` reads the state.
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

// §9.7 with A.8.2: `p.await;` waits as `p.await();` does.
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

// §9.7: a process created by an initial procedure that runs to its end has
// terminated normally, whether it last waited on an event or a delay.
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

// §9.7: await() on a process created by an initial procedure returns when
// that process ends.
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

// §9.7: the process is suspended before suspend() returns, so one suspending
// itself goes no further until another resumes it, and then continues in that
// time step.
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

// §9.7: a process suspended in a delay is desensitized to it. Resumed after
// the delay has expired it continues at once; resumed before, the delay
// expires on time.
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

// §9.7: a process suspended while waiting on an event is desensitized to it,
// so a trigger during the suspension passes it by; resume() resensitizes it and
// the next trigger wakes it.
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

// §9.7 with §6.19.5.6: a module variable declared process::state holds a
// member of that enumeration, so name() answers the member's name there as it
// does for a procedural variable of the same type.
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

}  // namespace
