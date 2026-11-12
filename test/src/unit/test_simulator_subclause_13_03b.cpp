#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TaskSim, GenerateBlockFunctionFormalReadsTheBlocksTypedefOverTheModules) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, ModuleFunctionBesideAShadowingBlockReadsTheModulesOwnTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "    return a.A.a;\n"
                      "  endfunction\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = f(tagged A '{7}) * 100"
                      " + g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            734u);
}

TEST(TaskSim,
     NestedGenerateBlockFunctionFormalReadsItsOwnTypedefOverTheOuters) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "    if (1) begin : h\n"
                      "      typedef struct { int a, b, c; } pair_t;\n"
                      "      function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 100 + a.A.b * 10 + a.A.c;\n"
                      "      endfunction\n"
                      "    end\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.h.f(tagged A '{1, 2, 3}) * 1000"
                      " + g.f(tagged A '{5, 6});\n"
                      "endmodule\n",
                      "y"),
            123056u);
}

TEST(TaskSim, GenerateBlockForwardTypedefStandsOverTheModulesTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, GenerateBlockForwardTypedefBelowItsDefinitionKeepsTheDefinition) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.b * 10 + a.A.a;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            43u);
}

TEST(TaskSim, GenerateBlockFunctionBelowANestedBlockReadsItsOwnTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b, c; } pair_t;\n"
                      "    if (1) begin : h\n"
                      "      typedef struct { int a, b; } pair_t;\n"
                      "      function int f2(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 10 + a.A.b;\n"
                      "      endfunction\n"
                      "    end\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 100 + a.A.b * 10 + a.A.c;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.h.f2(tagged A '{1, 2}) * 1000"
                      " + g.f(tagged A '{1, 2, 3});\n"
                      "endmodule\n",
                      "y"),
            12123u);
}

struct ElementTaskShape {
  std::string_view members;
  std::string_view decl;
  std::string_view setup;
  std::string_view elem;
  std::string_view reader;
};

static std::string ElementTaskDesign(const ElementTaskShape& shape) {
  std::string r(shape.reader);
  return "class C;\n"
         "  int v = 1;\n"
         "  task run(); #10; v = 5; endtask\n"
         "  function int get(); return v; endfunction\n" +
         std::string(shape.members) +
         "endclass\n"
         "module t;\n"
         "  int at5, at15, done_at, y;\n" +
         std::string(shape.decl) + "  initial begin\n" +
         std::string(shape.setup) +
         "    fork\n"
         "      begin " +
         std::string(shape.elem) + ".run(); done_at = $time; end\n" +
         "      begin #5 at5 = " + r + ".get(); #10 at15 = " + r +
         ".get(); end\n"
         "    join\n"
         "    y = at5 * 10000 + at15 * 100 + done_at;\n"
         "  end\n"
         "endmodule\n";
}

TEST(TaskSim, ClassTaskEnabledThroughAnArrayElementConsumesItsDelay) {
  EXPECT_EQ(
      RunAndGet(ElementTaskDesign({"", "  C arr[2];\n", "    arr[0] = new;\n",
                                   "arr[0]", "arr[0]"}),
                "y"),
      10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAQueueElementConsumesItsDelay) {
  EXPECT_EQ(
      RunAndGet(ElementTaskDesign({"",
                                   "  C q[$];\n"
                                   "  C c = new;\n",
                                   "    q.push_back(c);\n", "q[0]", "q[0]"}),
                "y"),
      10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAnAssocElementConsumesItsDelay) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign({"", "  C aa[string];\n",
                                         "    aa[\"k\"] = new;\n", "aa[\"k\"]",
                                         "aa[\"k\"]"}),
                      "y"),
            10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughACallResultConsumesItsDelay) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign(
                          {"  function C self(); return this; endfunction\n",
                           "  C c = new;\n", "", "c.self()", "c"}),
                      "y"),
            10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAnElementsPropertyConsumesItsDelay) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign({"",
                                         "  class H; C kid = new; endclass\n"
                                         "  H arr[2];\n"
                                         "  C k;\n",
                                         "    arr[0] = new;\n"
                                         "    k = arr[0].kid;\n",
                                         "arr[0].kid", "k"}),
                      "y"),
            10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAFunctionResultRunsOnItsObject) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign(
                          {"  C kid;\n"
                           "  function C get_kid(); return kid; endfunction\n",
                           "  C c = new;\n"
                           "  C k;\n",
                           "    c.kid = new;\n"
                           "    k = c.kid;\n",
                           "c.get_kid()", "k"}),
                      "y"),
            10510u);
}

TEST(TaskSim, BodyDeclarationTypesADirectionOnlyFormal) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  task mytask2;\n"
                      "    output x;\n"
                      "    input y;\n"
                      "    int x;\n"
                      "    int y;\n"
                      "    x = y * 3;\n"
                      "  endtask\n"
                      "  initial mytask2(r, 7);\n"
                      "endmodule\n",
                      "r"),
            21u);
}

std::string BlockingTaskRun(const std::string& src) {
  SimFixture f;
  std::string out = RunCaptureAllTops(src, f);
  EXPECT_EQ(f.diag.WarningCount(), 0u) << src;
  return out;
}

TEST(TaskSim, AModuleTaskWaitingOnAConditionReturnsWhenItBecomesTrue) {
  EXPECT_EQ(BlockingTaskRun("module m;\n"
                            "  bit go;\n"
                            "  int x;\n"
                            "  task t(); wait (go); endtask\n"
                            "  initial begin t(); x = $time; "
                            "$display(\"%0d\", x); end\n"
                            "  initial #7 go = 1;\n"
                            "endmodule\n"),
            "7\n");
}

TEST(TaskSim, AnInterfaceTaskEnabledThroughAPortReturnsAfterItsEdgeOrWait) {
  EXPECT_EQ(BlockingTaskRun("interface i(input logic clk);\n"
                            "  bit go;\n"
                            "  task te(); @(posedge clk); endtask\n"
                            "  task tw(); wait (go); endtask\n"
                            "endinterface\n"
                            "module n(i b);\n"
                            "  int x, y;\n"
                            "  initial begin\n"
                            "    b.te(); x = $time; b.tw(); y = $time;\n"
                            "    $display(\"%0d %0d\", x, y);\n"
                            "  end\n"
                            "endmodule\n"
                            "module m;\n"
                            "  logic clk = 0;\n"
                            "  i u(clk);\n"
                            "  n k(u);\n"
                            "  initial begin #5 clk = 1; #7 u.go = 1; end\n"
                            "endmodule\n"),
            "5 12\n");
}

TEST(TaskSim, AProgramTaskReturnsAfterItsEdgeOrWait) {
  EXPECT_EQ(BlockingTaskRun("program p;\n"
                            "  logic clk = 0;\n"
                            "  bit go;\n"
                            "  int x, y;\n"
                            "  task te(); @(posedge clk); endtask\n"
                            "  task tw(); wait (go); endtask\n"
                            "  initial begin\n"
                            "    te(); x = $time; tw(); y = $time;\n"
                            "    $display(\"%0d %0d\", x, y);\n"
                            "  end\n"
                            "  initial begin #5 clk = 1; #7 go = 1; end\n"
                            "endprogram\n"),
            "5 12\n");
}

TEST(TaskSim, APackageTaskReturnsAfterItsEventOrWait) {
  EXPECT_EQ(BlockingTaskRun("package p;\n"
                            "  event e;\n"
                            "  bit go;\n"
                            "  task te(); @(e); endtask\n"
                            "  task tw(); wait (go); endtask\n"
                            "  task fire(); ->e; endtask\n"
                            "endpackage\n"
                            "module m;\n"
                            "  int x, y;\n"
                            "  initial begin\n"
                            "    p::te(); x = $time; p::tw(); y = $time;\n"
                            "    $display(\"%0d %0d\", x, y);\n"
                            "  end\n"
                            "  initial begin #4 p::fire(); #5 p::go = 1; end\n"
                            "endmodule\n"),
            "4 9\n");
}

TEST(TaskSim, ACompilationUnitTaskReturnsAfterItsEventOrWait) {
  EXPECT_EQ(BlockingTaskRun("event e;\n"
                            "bit go;\n"
                            "task te(); @(e); endtask\n"
                            "task tw(); wait (go); endtask\n"
                            "module m;\n"
                            "  int x, y;\n"
                            "  initial begin\n"
                            "    te(); x = $time; tw(); y = $time;\n"
                            "    $display(\"%0d %0d\", x, y);\n"
                            "  end\n"
                            "  initial begin #4 ->e; #5 go = 1; end\n"
                            "endmodule\n"),
            "4 9\n");
}

TEST(TaskExampleSim,
     TheMyTaskExampleCopiesArgumentsInAndResultsOutInBothForms) {
  EXPECT_EQ(BlockingTaskRun("module m;\n"
                            "  logic v, w, x, y, z, x2, y2, z2;\n"
                            "  task my_task;\n"
                            "    input a, b;\n"
                            "    inout c;\n"
                            "    output d, e;\n"
                            "    c = a;\n"
                            "    d = b;\n"
                            "    e = c;\n"
                            "  endtask\n"
                            "  task my_task2 (input a, b, inout c, output d, "
                            "e);\n"
                            "    c = a;\n"
                            "    d = b;\n"
                            "    e = c;\n"
                            "  endtask\n"
                            "  initial begin\n"
                            "    v = 1; w = 0; x = 0; x2 = 0;\n"
                            "    my_task (v, w, x, y, z);\n"
                            "    my_task2 (v, w, x2, y2, z2);\n"
                            "    $display(\"%b%b%b %b%b%b\", x, y, z, x2, y2, "
                            "z2);\n"
                            "  end\n"
                            "endmodule\n"),
            "101 101\n");
}

TEST(TaskExampleSim, TheTrafficLightExampleTurnsEachLightOffAfterItsTics) {
  EXPECT_EQ(
      BlockingTaskRun(
          "module traffic_lights;\n"
          "  logic clock, red, amber, green;\n"
          "  parameter on = 1, off = 0, red_tics = 350,\n"
          "            amber_tics = 30, green_tics = 200;\n"
          "  initial red = off;\n"
          "  initial amber = off;\n"
          "  initial green = off;\n"
          "  always begin\n"
          "    red = on;\n"
          "    light(red, red_tics);\n"
          "    green = on;\n"
          "    light(green, green_tics);\n"
          "    amber = on;\n"
          "    light(amber, amber_tics);\n"
          "  end\n"
          "  task light (output color, input [31:0] tics);\n"
          "    repeat (tics) @ (posedge clock);\n"
          "    color = off;\n"
          "  endtask: light\n"
          "  always begin\n"
          "    #100 clock = 0;\n"
          "    #100 clock = 1;\n"
          "  end\n"
          "endmodule: traffic_lights\n"
          "module top;\n"
          "  traffic_lights #(.red_tics(3), .green_tics(2), .amber_tics(1)) "
          "t();\n"
          "  initial begin\n"
          "    @(posedge t.green) $display(\"green on %0t\", $time);\n"
          "    @(negedge t.green) $display(\"green off %0t\", $time);\n"
          "    @(negedge t.amber) $display(\"amber off %0t\", $time);\n"
          "    $finish(0);\n"
          "  end\n"
          "endmodule\n"),
      "green on 600\ngreen off 1000\namber off 1200\n");
}

}  // namespace
