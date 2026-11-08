#include <gtest/gtest.h>

#include <string>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 4, "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 5, "13.4"));
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' has output argument; cannot be called "
                    "in a continuous assignment",
                    5, "13.4"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' has inout argument; cannot be called "
                            "in a continuous assignment",
                            5, "13.4"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' has ref argument; cannot be called "
                            "in a continuous assignment",
                            5, "13.4"));
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' has output argument; cannot be called "
                    "in an event expression",
                    5, "13.4"));
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' has output argument; cannot be called "
                    "in a procedural continuous assignment",
                    6, "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only fork/join_none is permitted inside a function", 3, "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only fork/join_none is permitted inside a function", 3, "13.4"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a function's dynamic_override_specifiers belong on a class "
      "method declaration, and an interface class takes none",
      2, "13.4"));
}

TEST(FunctionElaboration, DynamicOverrideFinalOnModuleScopeFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :final void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a function's dynamic_override_specifiers belong on a class "
      "method declaration, and an interface class takes none",
      2, "13.4"));
}

TEST(FunctionElaboration, DynamicOverrideExtendsOnModuleScopeFunctionError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  function :initial :extends void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a function's dynamic_override_specifiers belong on a class "
      "method declaration, and an interface class takes none",
      2, "13.4"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only fork/join_none is permitted inside a function", 4, "13.4"));
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

TEST(FunctionElaboration, TaskEnabledFromAForStepError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f(input int n);\n"
      "    int i;\n"
      "    for (i = 0; i < n; t()) ;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 5, "13.4"));
}

constexpr const char* kForkStmt = "fork t = 1; join_none";
constexpr const char* kNbaStmt = "t <= 1;";
constexpr const char* kEventTriggerStmt = "-> ev;";
constexpr const char* kLocalDeclStmt = "begin int u; u = 1; end";
constexpr const char* kModuleVarStmt = "t = i;";

constexpr const char* kForkMsg =
    "constant function 'cf' uses fork, which constant functions are barred "
    "from";
constexpr const char* kNbaMsg =
    "constant function 'cf' shall not contain nonblocking assignments";
constexpr const char* kEventMsg =
    "constant function 'cf' schedules an event that would run once it has "
    "returned, which constant functions are barred from";
constexpr const char* kIdentMsg =
    "constant function 'cf' references identifier 'i' that is not a parameter, "
    "function name, or local declaration";

std::string ConstFuncSrc(const std::string& body) {
  return std::string(
             "module m;\n"
             "  event ev;\n"
             "  int i;\n"
             "  function int cf(input int n);\n"
             "    int t;\n") +
         body +
         "\n    return n;\n"
         "  endfunction\n"
         "  localparam int P = cf(1);\n"
         "endmodule\n";
}

void ExpectConstFuncError(const std::string& body, const std::string& message) {
  ElabFixture f;
  std::string src = ConstFuncSrc(body);
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, "localparam int P"), "13.4.3"));
}

void ExpectConstFuncAccepted(const std::string& body) {
  ElabFixture f;
  auto* design = ElaborateSrc(ConstFuncSrc(body), f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

std::string InAssertPassStmt(const std::string& stmt) {
  return "    assert (n) " + stmt;
}

std::string InAssertFailStmt(const std::string& stmt) {
  return "    assert (n) else " + stmt;
}

std::string InRandcaseItem(const std::string& stmt) {
  return "    randcase 1: " + stmt + " endcase";
}

std::string InRandsequenceCodeBlock(const std::string& stmt) {
  return "    randsequence(main)\n      main : { " + stmt +
         " };\n    endsequence";
}

std::string InRandsequenceWeightCodeBlock(const std::string& stmt) {
  return "    randsequence(main)\n      main : alt := 1 { " + stmt +
         " };\n      alt : { t = 0; };\n    endsequence";
}

TEST(ConstantFunctionBodyReachElaboration, ForkInAnAssertionPassStmt) {
  ExpectConstFuncError(InAssertPassStmt(kForkStmt), kForkMsg);
}

TEST(ConstantFunctionBodyReachElaboration, ForkInAnAssertionFailStmt) {
  ExpectConstFuncError(InAssertFailStmt(kForkStmt), kForkMsg);
}

TEST(ConstantFunctionBodyReachElaboration, ForkInARandcaseItem) {
  ExpectConstFuncError(InRandcaseItem(kForkStmt), kForkMsg);
}

TEST(ConstantFunctionBodyReachElaboration, ForkInARandsequenceCodeBlock) {
  ExpectConstFuncError(InRandsequenceCodeBlock(kForkStmt), kForkMsg);
}

TEST(ConstantFunctionBodyReachElaboration, ForkInARandsequenceWeightCodeBlock) {
  ExpectConstFuncError(InRandsequenceWeightCodeBlock(kForkStmt), kForkMsg);
}

TEST(ConstantFunctionBodyReachElaboration, NonblockingInAnAssertionPassStmt) {
  ExpectConstFuncError(InAssertPassStmt(kNbaStmt), kNbaMsg);
}

TEST(ConstantFunctionBodyReachElaboration, NonblockingInAnAssertionFailStmt) {
  ExpectConstFuncError(InAssertFailStmt(kNbaStmt), kNbaMsg);
}

TEST(ConstantFunctionBodyReachElaboration, NonblockingInARandcaseItem) {
  ExpectConstFuncError(InRandcaseItem(kNbaStmt), kNbaMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     NonblockingInARandsequenceCodeBlock) {
  ExpectConstFuncError(InRandsequenceCodeBlock(kNbaStmt), kNbaMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     NonblockingInARandsequenceWeightCodeBlock) {
  ExpectConstFuncError(InRandsequenceWeightCodeBlock(kNbaStmt), kNbaMsg);
}

TEST(ConstantFunctionBodyReachElaboration, EventTriggerInAnAssertionPassStmt) {
  ExpectConstFuncError(InAssertPassStmt(kEventTriggerStmt), kEventMsg);
}

TEST(ConstantFunctionBodyReachElaboration, EventTriggerInAnAssertionFailStmt) {
  ExpectConstFuncError(InAssertFailStmt(kEventTriggerStmt), kEventMsg);
}

TEST(ConstantFunctionBodyReachElaboration, EventTriggerInARandcaseItem) {
  ExpectConstFuncError(InRandcaseItem(kEventTriggerStmt), kEventMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     EventTriggerInARandsequenceCodeBlock) {
  ExpectConstFuncError(InRandsequenceCodeBlock(kEventTriggerStmt), kEventMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     EventTriggerInARandsequenceWeightCodeBlock) {
  ExpectConstFuncError(InRandsequenceWeightCodeBlock(kEventTriggerStmt),
                       kEventMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     ModuleVariableReadInAnAssertionPassStmt) {
  ExpectConstFuncError(InAssertPassStmt(kModuleVarStmt), kIdentMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     ModuleVariableReadInAnAssertionFailStmt) {
  ExpectConstFuncError(InAssertFailStmt(kModuleVarStmt), kIdentMsg);
}

TEST(ConstantFunctionBodyReachElaboration, ModuleVariableReadInARandcaseItem) {
  ExpectConstFuncError(InRandcaseItem(kModuleVarStmt), kIdentMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     ModuleVariableReadInARandsequenceCodeBlock) {
  ExpectConstFuncError(InRandsequenceCodeBlock(kModuleVarStmt), kIdentMsg);
}

TEST(ConstantFunctionBodyReachElaboration,
     ModuleVariableReadInARandsequenceWeightCodeBlock) {
  ExpectConstFuncError(InRandsequenceWeightCodeBlock(kModuleVarStmt),
                       kIdentMsg);
}

TEST(ConstantFunctionBodyReachElaboration, LocalDeclInAnAssertionPassStmt) {
  ExpectConstFuncAccepted(InAssertPassStmt(kLocalDeclStmt));
}

TEST(ConstantFunctionBodyReachElaboration, LocalDeclInAnAssertionFailStmt) {
  ExpectConstFuncAccepted(InAssertFailStmt(kLocalDeclStmt));
}

TEST(ConstantFunctionBodyReachElaboration, LocalDeclInARandcaseItem) {
  ExpectConstFuncAccepted(InRandcaseItem(kLocalDeclStmt));
}

TEST(ConstantFunctionBodyReachElaboration, LocalDeclInARandsequenceCodeBlock) {
  ExpectConstFuncAccepted(InRandsequenceCodeBlock(kLocalDeclStmt));
}

TEST(ConstantFunctionBodyReachElaboration,
     LocalDeclInARandsequenceWeightCodeBlock) {
  ExpectConstFuncAccepted(InRandsequenceWeightCodeBlock(kLocalDeclStmt));
}

std::string InRandsequence(const std::string& rules) {
  return "    randsequence(main)\n      main : " + rules +
         ";\n      a : { t = 0; };\n      b : { t = 0; };\n"
         "      c(int x) : { t = 0; };\n    endsequence";
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInAnIntraAssignmentEventSignal) {
  ExpectConstFuncError("    t = @(i) 1;", kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInAnIntraAssignmentEventIff) {
  ExpectConstFuncError("    t = @(n iff i) 1;", kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration, ModuleVariableInARandcaseWeight) {
  ExpectConstFuncError("    randcase i: t = 1; endcase", kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInAnUnpackedDimension) {
  ExpectConstFuncError("    int u[i];", kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceWeight) {
  ExpectConstFuncError(InRandsequence("a := i"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration, ModuleVariableInARandJoinExpr) {
  ExpectConstFuncError(InRandsequence("rand join (i) a b"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandJoinItemArgument) {
  ExpectConstFuncError(InRandsequence("rand join (1) c(i) a"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceItemArgument) {
  ExpectConstFuncError(InRandsequence("c(i)"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceIfCondition) {
  ExpectConstFuncError(InRandsequence("if (i) a"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceIfItemArgument) {
  ExpectConstFuncError(InRandsequence("if (n) c(i)"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceElseItemArgument) {
  ExpectConstFuncError(InRandsequence("if (n) a else c(i)"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceRepeatCount) {
  ExpectConstFuncError(InRandsequence("repeat (i) a"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceRepeatItemArgument) {
  ExpectConstFuncError(InRandsequence("repeat (n) c(i)"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceCaseExpr) {
  ExpectConstFuncError(InRandsequence("case (i) 1: a; endcase"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceCaseItemExpr) {
  ExpectConstFuncError(InRandsequence("case (n) i: a; endcase"), kIdentMsg);
}

TEST(ConstantFunctionExprReachElaboration,
     ModuleVariableInARandsequenceCaseItemArgument) {
  ExpectConstFuncError(InRandsequence("case (n) 1: c(i); endcase"), kIdentMsg);
}

}  // namespace
