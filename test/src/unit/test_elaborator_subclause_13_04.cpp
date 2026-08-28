#include <string>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
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
  // §8.20 is the rule that rejects this, not §13.4: the specifier parses on any
  // subroutine, and the elaborator refuses it outside a class scope.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "dynamic_override_specifiers shall only be legal on method declarations",
      2, "8.20"));
}

TEST(FunctionElaboration, DynamicOverrideFinalOnModuleScopeFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :final void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  // §8.20 is the rule that rejects this, not §13.4.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "dynamic_override_specifiers shall only be legal on method declarations",
      2, "8.20"));
}

TEST(FunctionElaboration, DynamicOverrideExtendsOnModuleScopeFunctionError) {
  ElabFixture f;
  // §8.20 is reported while parsing, so the source does not parse and the
  // permissive helper is what records that.
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  function :initial :extends void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  // §8.20 is the rule that rejects this, not §13.4.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "dynamic_override_specifiers shall only be legal on method declarations",
      2, "8.20"));
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

// §13.4.3 lists the constraints a constant function is held to, and none of
// them says where in the body the statement or expression breaking one may
// stand. Five walks in src/elaborator/elaborator_validate_funcchecks.cpp
// enforce them — BodyContainsFork and BodyContainsNonblocking and
// BodyContainsEventScheduling for "shall not contain any fork constructs" and
// "shall not contain a statement that directly schedules an event to execute
// after the function has returned", CollectLocalDeclNames and
// WalkConstFuncStmt for "shall not reference any identifiers that are not
// either parameter or function names, or declared locally to the current
// function" — and each had written out a short list of its own of the thirteen
// child-statement links Stmt declares. They now take the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h, and the
// cases below cover the positions that reaches which their own lists did not.
//
// Five positions are newly reached, and each walk gets one case per position.
// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. §18.16 gives
// `randcase_item ::= expression : statement_or_null`, whose statement the
// parser keeps in the second member of a Stmt::randcase_items entry. A.6.12
// gives `rs_code_block ::= { { data_declaration } { statement_or_null } }`,
// reached from an rs_prod as RsProd::code_stmts and, per §18.17.1, from after a
// weight specification as RsRule::weight_code; both hang off
// Stmt::rs_productions, and a walk reaches one without reaching the other.
//
// §18.17.6 gives break and return a meaning inside a randsequence production
// code block that they have nowhere else, and none of these five walks is about
// break or return, so each is owed inside one.
//
// Stmt::fork_stmts, Stmt::for_inits and Stmt::for_steps get no case. A.6.8
// admits only a variable_assignment or a for_variable_declaration in a
// for_initialization and only an operator_assignment, an inc_or_dec_expression
// or a function_subroutine_call in a for_step, so neither can hold a fork, a
// nonblocking assignment, a timing control or a declaration.
// src/parser/parser_stmt_block.cpp fills Stmt::fork_stmts on a StmtKind::kFork
// alone, so BodyContainsFork answers at that fork before descending, and
// §13.4.3's "shall not contain any fork constructs" stops the other four walks
// before they see the inside of one.
//
// These cases cover §13.4.3 and belong in
// test/src/unit/test_elaborator_subclause_13_04_03.cpp. They stand here because
// that file is at 908 lines against the 1000-line maximum
// .github/workflows/deltahdl.yml enforces.

// The statement each walk is looking for, written once and placed by the
// helpers below into each of the five positions.
constexpr const char* kForkStmt = "fork t = 1; join_none";
constexpr const char* kNbaStmt = "t <= 1;";
constexpr const char* kEventTriggerStmt = "-> ev;";
constexpr const char* kLocalDeclStmt = "begin int u; u = 1; end";
constexpr const char* kModuleVarStmt = "t = i;";

// What each walk's rule reports, with the function named `cf` by ConstFuncSrc.
constexpr const char* kForkMsg =
    "constant function 'cf' shall not contain fork";
constexpr const char* kNbaMsg =
    "constant function 'cf' shall not contain nonblocking assignments";
constexpr const char* kEventMsg =
    "constant function 'cf' shall not contain statements that schedule events "
    "to execute after it returns";
constexpr const char* kIdentMsg =
    "constant function 'cf' references identifier 'i' that is not a parameter, "
    "function name, or local declaration";

// One module holding `body` as the whole of a constant function's body between
// its own `int t;` declaration and its return. §13.4.3 holds of a function
// called where a constant expression is required, so `cf` is called from a
// localparam initializer, and every report below stands at that call rather
// than at the offending statement.
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

// The companion to ExpectConstFuncError for CollectLocalDeclNames, whose rule
// is that a name declared in the position is in scope rather than that a
// statement there is rejected. Without the collection reaching the position,
// WalkConstFuncStmt reaches the use and reports the name as declared nowhere.
void ExpectConstFuncAccepted(const std::string& body) {
  ElabFixture f;
  auto* design = ElaborateSrc(ConstFuncSrc(body), f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The five positions, each placing `stmt` where the old lists did not look.
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

}  // namespace
