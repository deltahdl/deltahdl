#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlSimulation, SelfReturnsHandle) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    x = (p != null) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, StatusRunningForCurrentProcess) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    x = (p.status() == process::RUNNING) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, KillTerminatesChild) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #10 x = 99;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(FineGrainProcessControlSimulation, AwaitWaitsForTermination) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #5 a = 1;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.await();\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 1u}});
}

TEST(FineGrainProcessControlSimulation, SuspendAndResume) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #1 x = 1;\n"
      "        #1 x = 2;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.suspend();\n"
      "    #10;\n"
      "    p.resume();\n"
      "    #5;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 2u}});
}

TEST(FineGrainProcessControlSimulation, StatusFinishedAfterTermination) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    x = (p.status() == process::FINISHED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, StatusKilledAfterKill) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    x = (p.status() == process::KILLED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, KillTerminatesDescendants) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        fork\n"
      "          #10 x = 99;\n"
      "        join_none\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(FineGrainProcessControlSimulation, ResumeNoEffectOnNonSuspended) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #5 x = 42;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.resume();\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(FineGrainProcessControlSimulation, SuspendNoEffectOnFinished) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.suspend();\n"
      "    x = (p.status() == process::FINISHED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

}  // namespace
