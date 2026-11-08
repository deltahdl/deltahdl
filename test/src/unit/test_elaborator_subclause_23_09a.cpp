#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

void ExpectLoopArrayNameConflictsWith(const std::string& module_level_decl) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "endmodule\n"
      "module top;\n"
      "  " +
          module_level_decl +
          "\n"
          "  genvar i;\n"
          "  for (i = 0; i < 2; i = i + 1) begin : a\n"
          "    wire w;\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'a' conflicts with an "
                            "existing declaration in the same scope",
                            6, "27.4"));
}

TEST(ScopeRulesElaboration, DuplicateIdentifierInSameScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire w;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 3, "6.5"));
}

TEST(ScopeRulesElaboration, DuplicateVariableDeclarationInSameScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int x;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "6.5"));
}

TEST(ScopeRulesElaboration, TaskNameMatchingVariableRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic foo;\n"
      "  task foo;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'foo'", 3, "23.9"));
}

TEST(ScopeRulesElaboration, GateInstanceNameMatchingOutputNetRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire a, b;\n"
      "  and g1(g1, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate instance name 'g1' conflicts with its "
                            "output net",
                            3, "23.9"));
}

TEST(ScopeRulesElaboration, SameNameInSeparateModuleScopesAllowed) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  wire x;\n"
             "endmodule\n"
             "module top;\n"
             "  wire x;\n"
             "  child c();\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, SameNameInPackageAndModuleScopesAllowed) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  int x;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, ConditionalGenerateBlocksAllowSameIdentifier) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter P = 1;\n"
             "  if (P == 1) begin : g\n"
             "    logic data;\n"
             "  end else begin : g\n"
             "    logic data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, DirectVariableReferenceStopsAtModuleBoundary) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  initial outer_x = 1;\n"
      "endmodule\n"
      "module parent;\n"
      "  logic outer_x;\n"
      "  child c();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier 'outer_x'", 2, "23.9"));
}

TEST(ScopeRulesElaboration, InstanceNamePrecedenceOverModuleTypeName) {
  EXPECT_TRUE(
      ElabOk("module foo;\n"
             "  integer x;\n"
             "endmodule\n"
             "module top;\n"
             "  foo foo();\n"
             "  initial foo.x = 5;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, DirectReferenceResolvesUpwardToEnclosingScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic sig;\n"
             "  initial begin : b\n"
             "    sig = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, DuplicateNamedBlockLabelsInSameScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin : b\n"
      "  end\n"
      "  initial begin : b\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'b'", 4, "23.9"));
}

TEST(ScopeRulesElaboration, DuplicateIdentifierNames23_9) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  function int w();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 3, "23.9"));
}

TEST(ScopeRulesElaboration, FunctionBodyDuplicateLocalError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function int f();\n"
      "    int x;\n"
      "    int x;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "23.9"));
}

TEST(ScopeRulesElaboration, TaskBodyDuplicateLocalError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  task t();\n"
      "    int y;\n"
      "    int y;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'y'", 4, "23.9"));
}

TEST(ScopeRulesElaboration,
     DuplicateLocalReportsOneSubclauseWhereverTheBlockSits) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function int fn();\n"
      "    int fn_dup;\n"
      "    int fn_dup;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int blk_dup;\n"
      "    int blk_dup;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'fn_dup'",
                            4, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'blk_dup'",
                            9, "23.9"));
}

TEST(ScopeRulesElaboration, DuplicateLocalInForkJoinError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial fork\n"
      "    int x;\n"
      "    int x;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "23.9"));
}

TEST(ScopeRulesElaboration, DuplicateLocalInForkJoinInsideFunctionError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function int fn();\n"
      "    fork\n"
      "      int x;\n"
      "      int x;\n"
      "    join_none\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 5, "23.9"));
}

TEST(ScopeRulesElaboration, SameLocalNameInForkAndEnclosingBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    int x;\n"
             "    fork\n"
             "      int x;\n"
             "    join\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration,
     DirectVariableReadInExpressionStopsAtModuleBoundary) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    r = v + 0;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            4, "23.9"));
}

TEST(ScopeRulesElaboration,
     DirectVariableReadInDeclarationInitializerStopsAtModuleBoundary) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  int q = v;\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            2, "23.9"));
}

TEST(ScopeRulesElaboration, DirectVariableReadInTaskBodyStopsAtModuleBoundary) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  integer r;\n"
      "  task t();\n"
      "    r = v;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            4, "23.9"));
}

TEST(ScopeRulesElaboration,
     DirectVariableReadStopsAtModuleBoundaryInModuleHoldingGenerateFor) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  integer r;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g\n"
      "    wire w;\n"
      "  end\n"
      "  initial r = v;\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            7, "23.9"));
}

TEST(ScopeRulesElaboration, BareNameSuppliedByAWildcardImportIsStillAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int pv;\n"
             "endpackage\n"
             "module m;\n"
             "  import p::*;\n"
             "  integer r;\n"
             "  initial begin\n"
             "    r = pv + 0;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, BareNameDeclaredInAGenerateBlockIsStillAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  integer r;\n"
             "  genvar i;\n"
             "  for (i = 0; i < 2; i = i + 1) begin : g\n"
             "    integer gv;\n"
             "    initial begin\n"
             "      r = gv + 0;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration,
     GenerateBlockDeclarationNamesDoNotCollideAcrossModules) {
  EXPECT_TRUE(
      ElabOk("module a;\n"
             "  if (1) begin : g\n"
             "    wire w;\n"
             "  end\n"
             "endmodule\n"
             "module b;\n"
             "  if (1) begin : g\n"
             "    wire w;\n"
             "  end\n"
             "endmodule\n"
             "module top;\n"
             "  a u_a();\n"
             "  b u_b();\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration,
     RepeatedInstantiationDoesNotRedeclareGenerateBlockNames) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  if (1) begin : g\n"
             "    wire w;\n"
             "  end\n"
             "endmodule\n"
             "module top;\n"
             "  child u1();\n"
             "  child u2();\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration,
     GenerateBlockArrayNameConflictingWithAnInstanceNameErrors) {
  ExpectLoopArrayNameConflictsWith("child a();");
}

TEST(ScopeRulesElaboration,
     GenerateBlockArrayNameConflictingWithAFunctionNameErrors) {
  ExpectLoopArrayNameConflictsWith("function void a(); endfunction");
}

void ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
    const std::string& prelude, const std::string& loop_body_item) {
  EXPECT_TRUE(ElabOk(prelude +
                     "module m;\n"
                     "  logic [7:0] d;\n"
                     "  wire [7:0] y;\n"
                     "  genvar i;\n"
                     "  for (i = 4; i < 6; i = i + 1) begin : b\n"
                     "    " +
                     loop_body_item +
                     "\n"
                     "  end\n"
                     "endmodule\n"));
}

TEST(ScopeRulesElaboration, LoopGenerateGateInstanceNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
      "", "and g (y[i], d[i], d[i]);");
}

TEST(ScopeRulesElaboration, LoopGenerateUdpInstanceNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
      "primitive udp_inv (y, a);\n"
      "  output y;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1 ;\n"
      "    1 : 0 ;\n"
      "  endtable\n"
      "endprimitive\n",
      "udp_inv g (y[i], d[i]);");
}

TEST(ScopeRulesElaboration, LoopGenerateFunctionNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
      "", "function int fn(); return 0; endfunction");
}

TEST(ScopeRulesElaboration, LoopGenerateTaskNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration("", "task tk(); endtask");
}

TEST(ScopeRulesElaboration, DuplicateGateInstanceNamesInOneScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire a, b, o1, o2;\n"
      "  and g (o1, a, b);\n"
      "  and g (o2, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'g'", 4, "23.9"));
}

void ExpectUndeclaredAssignTargetIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  logic ok;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'z'",
                            LineHolding(src, "z = 1;"), "23.9"));
}

TEST(ScopeRulesElaboration, UndeclaredAssignTargetInAnAssertionPassStmt) {
  ExpectUndeclaredAssignTargetIn("assert (ok) z = 1;");
}

TEST(ScopeRulesElaboration, UndeclaredAssignTargetInAnAssertionFailStmt) {
  ExpectUndeclaredAssignTargetIn("assert (ok) else z = 1;");
}

TEST(ScopeRulesElaboration, UndeclaredAssignTargetInARandcaseItem) {
  ExpectUndeclaredAssignTargetIn("randcase 1: z = 1; endcase");
}

TEST(ScopeRulesElaboration, UndeclaredAssignTargetInARandsequenceCodeBlock) {
  ExpectUndeclaredAssignTargetIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { z = 1; };\n"
      "      endsequence\n"
      "    end");
}

TEST(ScopeRulesElaboration,
     UndeclaredAssignTargetInARandsequenceWeightCodeBlock) {
  ExpectUndeclaredAssignTargetIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { z = 1; };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

void ExpectDuplicateBlockLocalIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  logic ok;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'a'",
                            LineHolding(src, "begin int a; int a; end"),
                            "23.9"));
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInAnAssertionPassStmt) {
  ExpectDuplicateBlockLocalIn("assert (ok) begin int a; int a; end");
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInAnAssertionFailStmt) {
  ExpectDuplicateBlockLocalIn("assert (ok) else begin int a; int a; end");
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInARandcaseItem) {
  ExpectDuplicateBlockLocalIn("randcase 1: begin int a; int a; end endcase");
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInARandsequenceCodeBlock) {
  ExpectDuplicateBlockLocalIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { begin int a; int a; end };\n"
      "      endsequence\n"
      "    end");
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInARandsequenceWeightCodeBlock) {
  ExpectDuplicateBlockLocalIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { begin int a; int a; end };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

void ExpectDuplicateTaskBlockLocalIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  task t();\n    " + stmt + "\n  endtask\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'a'",
                            LineHolding(src, "begin int a; int a; end"),
                            "23.9"));
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInATaskAssertionPassStmt) {
  ExpectDuplicateTaskBlockLocalIn("assert (1) begin int a; int a; end");
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInATaskAssertionFailStmt) {
  ExpectDuplicateTaskBlockLocalIn("assert (1) else begin int a; int a; end");
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInATaskRandcaseItem) {
  ExpectDuplicateTaskBlockLocalIn(
      "randcase 1: begin int a; int a; end endcase");
}

TEST(ScopeRulesElaboration, DuplicateBlockLocalInATaskRandsequenceCodeBlock) {
  ExpectDuplicateTaskBlockLocalIn(
      "randsequence(main)\n"
      "      main : { begin int a; int a; end };\n"
      "    endsequence");
}

TEST(ScopeRulesElaboration,
     DuplicateBlockLocalInATaskRandsequenceWeightCodeBlock) {
  ExpectDuplicateTaskBlockLocalIn(
      "randsequence(main)\n"
      "      main : alt := 5 { begin int a; int a; end };\n"
      "      alt : { ; };\n"
      "    endsequence");
}

struct UnitConstantWrite {
  const char* src;
  const char* message;
  const char* subclause;
};

TEST(ScopeRulesElaboration, AWrittenCompilationUnitConstantIsNotUndeclared) {
  const UnitConstantWrite kWrites[] = {
      {"parameter int G = 1;\nmodule m;\n  initial G = 2;\nendmodule\n",
       "assignment to constant 'G'", "6.20"},
      {"localparam int G = 1;\nmodule m;\n  initial G = 2;\nendmodule\n",
       "assignment to constant 'G'", "6.20"},
      {"parameter int G = 1;\nmodule m;\n  initial $unit::G = 2;\n"
       "endmodule\n",
       "assignment to constant '$unit::G'", "6.20"},
      {"typedef enum {G, H} e_t;\nmodule m;\n  initial G = H;\nendmodule\n",
       "assignment of constant 'G', which is not a variable", "10.4"},
  };
  for (const UnitConstantWrite& write : kWrites) {
    SCOPED_TRACE(write.src);
    ElabFixture f;
    ElaborateSrc(write.src, f);
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "undeclared identifier", 3,
                               "23.9"));
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), write.message, 3, write.subclause));
  }
}

TEST(ScopeRulesElaboration,
     ATargetTheCompilationUnitDoesNotDeclareIsUndeclared) {
  ElabFixture f;
  ElaborateSrc(
      "parameter int G = 1;\n"
      "module m;\n"
      "  initial H = 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'H'",
                            3, "23.9"));
}

}  // namespace
