#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FunctionElaboration, FunctionWithOutputArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void compute(input int a, output int b);\n"
      "    b = a * 2;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithRefArgElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic void inc(ref int v);\n"
      "    v = v + 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionEmptyBodyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void nop();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithDelayError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    #10;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionEnablesTaskError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f();\n"
      "    t();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, EventControlInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  function void f();\n"
      "    @(posedge clk);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, WaitInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic ready;\n"
      "  function void f();\n"
      "    wait(ready);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, WaitForkInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    wait fork;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, WaitOrderInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e1, e2;\n"
      "  function void f();\n"
      "    wait_order(e1, e2);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, NestedDelayInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      #5;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithNoTimeControlIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionCallsFunctionIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int g(); return 0; endfunction\n"
      "  function int f(); return g(); endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionCallsSystemTaskOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    $display(\"hello\");\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithNestedTaskEnableError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      t();\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, OutputArgCallInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(output int b); b = 7; return 0; endfunction\n"
      "  int v;\n"
      "  wire [31:0] w;\n"
      "  assign w = f(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, InoutArgCallInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(inout int b); return b; endfunction\n"
      "  int v;\n"
      "  wire [31:0] w;\n"
      "  assign w = f(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, RefArgCallInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function automatic int f(ref int b); return b; endfunction\n"
      "  int v;\n"
      "  wire [31:0] w;\n"
      "  assign w = f(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, ConstRefArgCallInContAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(const ref int b); return b; endfunction\n"
      "  int v;\n"
      "  wire [31:0] w;\n"
      "  assign w = f(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, OutputArgCallInEventExpressionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(output int b); b = 0; return 0; endfunction\n"
      "  int v;\n"
      "  logic clk;\n"
      "  always @(posedge clk iff f(v) != 0) v = v + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, OutputArgCallInProceduralContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(output int b); b = 0; return 0; endfunction\n"
      "  int v;\n"
      "  logic [31:0] w;\n"
      "  initial begin\n"
      "    assign w = f(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithExpectError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic ready;\n"
      "  function void f();\n"
      "    expect(ready);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithCycleDelayError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    ##5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, ImplicitReturnTypeIsLogicScalar) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function foo();\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  logic x;\n"
      "  initial x = foo();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithForkJoinError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      ;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithForkJoinAnyError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      ;\n"
      "    join_any\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4 rule a) enumerates fork-join and fork-join_any (alongside #, ##, @,
// wait, wait fork, wait_order, and expect) as the time-controlling statements a
// function shall not contain. fork-join_none is deliberately absent from that
// list: it spawns background processes without suspending the enclosing
// function, so it stays legal. This is the same restriction §9.3.2 refers to
// when it notes that a parallel block has restricted usage inside function
// calls (see 13.4). This positive case makes the negative fork-join and
// fork-join_any tests above discriminating on the join keyword rather than on
// the mere presence of a fork.
TEST(FunctionElaboration, FunctionWithForkJoinNoneIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      ;\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionMayCallProcessKill) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.kill();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionMayCallProcessSuspendResume) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f(process p);\n"
      "    p.suspend();\n"
      "    p.resume();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, DynamicOverrideOnModuleScopeFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :initial void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, DynamicOverrideFinalOnModuleScopeFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :final void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, DynamicOverrideExtendsOnModuleScopeFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :initial :extends void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, NestedForkJoinInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      fork\n"
      "        ;\n"
      "      join\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, InputOnlyArgCallInContAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(input int a); return a + 1; endfunction\n"
      "  wire [31:0] w;\n"
      "  assign w = f(32'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
