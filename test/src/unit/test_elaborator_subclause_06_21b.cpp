#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.21's top_illegal example: in a static procedural block, a variable
// declared with an initializer states whether it is static or automatic, and
// `int loop3 = 0;` in a loop body states neither, so it is reported where it is
// declared and nothing else is.
TEST(LifetimeIntentElaboration, InitializedLoopLocalInAnInitialReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top_illegal;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 3; i++) begin\n"
      "      int loop3 = 0;\n"
      "      for (int j = 0; j < 3; j++) begin\n"
      "        loop3++;\n"
      "        $display(loop3);\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'loop3' declared with an initializer in "
                            "a static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §6.21's top_legal example: the same loop bodies with `automatic`, run on
// each iteration, and with `static`, run once, state the intent.
TEST(LifetimeIntentElaboration, LoopLocalsWithAStatedLifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("module top_legal;\n"
             "  initial begin\n"
             "    for (int i = 0; i < 3; i++) begin\n"
             "      automatic int loop3 = 0;\n"
             "      loop3++;\n"
             "    end\n"
             "    for (int i = 0; i < 3; i++) begin\n"
             "      static int loop2 = 0;\n"
             "      loop2++;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

// A loop local without an initializer has no initialization whose timing is
// in question, so the rule does not reach it.
TEST(LifetimeIntentElaboration, UninitializedLoopLocalAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    repeat (3) begin\n"
             "      int n;\n"
             "      n = 1;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

// A while loop's body is a loop body as a for loop's is, and a task written
// with no lifetime in a module that writes none is static, so its loop local
// with an initializer is reported too.
TEST(LifetimeIntentElaboration, InitializedLocalInAStaticTaskLoopReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  task tk;\n"
      "    while (1) begin\n"
      "      int k = 2;\n"
      "      break;\n"
      "    end\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'k' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
}

// An automatic task's variables are automatic by default (§6.21), and so are
// a `module automatic`'s blocks', so neither loop local needs a keyword.
TEST(LifetimeIntentElaboration,
     InitializedLoopLocalInAnAutomaticScopeAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic tk;\n"
             "    forever begin\n"
             "      int k = 2;\n"
             "      break;\n"
             "    end\n"
             "  endtask\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module automatic m;\n"
             "  initial begin\n"
             "    do begin\n"
             "      int k = 2;\n"
             "    end while (0);\n"
             "  end\n"
             "endmodule\n"));
}

// §6.21's top_illegal example also marks `int svar2 = 2;` at the top of an
// initial block, outside any loop: the block is static, so the declaration
// shall say whether its initializer runs once or on each entry.
TEST(LifetimeIntentElaboration, InitializedLocalAtTheTopOfAnInitialReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top_illegal;\n"
      "  initial begin\n"
      "    int svar2 = 2;\n"
      "    $display(svar2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'svar2' declared with an initializer in "
                            "a static block, task or function must be declared "
                            "static or automatic",
                            3, "6.21"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §6.21's top_legal example writes the same declaration `static`, and
// `automatic` states the other intent; either keyword satisfies the rule.
TEST(LifetimeIntentElaboration, TopLevelLocalsWithAStatedLifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("module top_legal;\n"
             "  initial begin\n"
             "    static int svar1 = 1;\n"
             "    automatic int avar1 = 1;\n"
             "    $display(svar1, avar1);\n"
             "  end\n"
             "endmodule\n"));
}

// A block parameter is a constant, not a variable (§6.20.1), so §6.21's rule
// on a variable's initializer does not reach it even though it is written with
// a value and no lifetime.
TEST(LifetimeIntentElaboration, BlockParameterWithAValueAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    localparam int W = 4;\n"
             "    parameter int D = 2;\n"
             "    $display(W, D);\n"
             "  end\n"
             "endmodule\n"));
}

// The blocks of a `module automatic` are automatic, and so is an automatic
// task's body in a module that states no lifetime, so neither declaration
// needs a keyword.
TEST(LifetimeIntentElaboration, InitializedLocalsInAutomaticScopesAccepted) {
  EXPECT_TRUE(
      ElabOk("module automatic m;\n"
             "  initial begin\n"
             "    int n = 1;\n"
             "    $display(n);\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic tk;\n"
             "    int n = 1;\n"
             "    $display(n);\n"
             "  endtask\n"
             "endmodule\n"));
}

// §18.17 makes a randsequence statement an automatic scope, and each code block
// within it another, so a code block's initialized local is automatic by
// default in a static initial block and needs no keyword.
TEST(LifetimeIntentElaboration,
     InitializedLocalInARandsequenceCodeBlockAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int av;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { int fresh = 0; fresh++; av = fresh; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

// A function with no lifetime in a module with none is static (§13.4.2), so
// its initialized local outside any loop is reported as a static task's is.
TEST(LifetimeIntentElaboration, InitializedLocalInAStaticFunctionReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  function int f();\n"
      "    int n = 1;\n"
      "    return n;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'n' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            3, "6.21"));
}

// A class method is automatic (§8.6), both written in its class and defined
// out of block with the class scope operator, so its initialized local
// needs no keyword.
TEST(LifetimeIntentElaboration, InitializedLocalInAClassMethodAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  function int f();\n"
             "    int n = 1;\n"
             "    return n;\n"
             "  endfunction\n"
             "  extern function int g();\n"
             "endclass\n"
             "function int C::g();\n"
             "  int n = 2;\n"
             "  return n;\n"
             "endfunction\n"
             "module t;\n"
             "  initial begin\n"
             "    static C c = new;\n"
             "    $display(c.f(), c.g());\n"
             "  end\n"
             "endmodule\n"));
}

// §27.3: an initial block a generate block brings into existence acts as it
// would in the module, so its initialized local is static and reported.
TEST(LifetimeIntentElaboration, InitializedLocalInAGenerateIfBlockReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    initial begin\n"
      "      int x = 1;\n"
      "      $display(x);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'x' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
}

// The same declaration saying `static`, and one inside a `module automatic`'s
// generate block, state a lifetime and are accepted.
TEST(LifetimeIntentElaboration, GenerateBlockLocalsWithALifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  if (1) begin : g\n"
             "    initial begin\n"
             "      static int x = 1;\n"
             "      $display(x);\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module automatic m;\n"
             "  if (1) begin : g\n"
             "    initial begin\n"
             "      int x = 1;\n"
             "      $display(x);\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

// A task with no lifetime inside a generate-for block of a module with none is
// static (§13.3.1, §27.3), so its initialized local is reported.
TEST(LifetimeIntentElaboration, InitializedLocalInAGenerateForTaskReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    task tk;\n"
      "      int n = 1;\n"
      "      $display(n);\n"
      "    endtask\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'n' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
}

// An else branch and a case generate arm hold their blocks apart from the
// construct's own body, so each is reached on its own.
TEST(LifetimeIntentElaboration, InitializedLocalsInElseAndCaseArmsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (0) begin : a\n"
      "  end else begin : b\n"
      "    initial begin\n"
      "      int e = 1;\n"
      "    end\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : c\n"
      "      initial begin\n"
      "        int k = 1;\n"
      "      end\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'e' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            5, "6.21"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'k' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            11, "6.21"));
}

// A package's function with no lifetime in a package with none is static
// (§13.4.2), so its initialized local is reported.
TEST(LifetimeIntentElaboration, InitializedLocalInAPackageFunctionReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  function int f();\n"
      "    int n = 1;\n"
      "    return n;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  initial $display(p::f());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'n' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            3, "6.21"));
}

// A lifetime on the declaration, on the function or on the package makes the
// package function's initialized local legal, and so does the function being
// a method of a class the package declares.
TEST(LifetimeIntentElaboration, PackageLocalsWithALifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  function int f();\n"
             "    static int s = 1;\n"
             "    automatic int a = 1;\n"
             "    return s + a;\n"
             "  endfunction\n"
             "endpackage\n"));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  function automatic int f();\n"
             "    int n = 1;\n"
             "    return n;\n"
             "  endfunction\n"
             "endpackage\n"));
  EXPECT_TRUE(
      ElabOk("package automatic p;\n"
             "  task tk;\n"
             "    int n = 1;\n"
             "    $display(n);\n"
             "  endtask\n"
             "endpackage\n"));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  class C;\n"
             "    function int f();\n"
             "      int n = 1;\n"
             "      return n;\n"
             "    endfunction\n"
             "  endclass\n"
             "endpackage\n"));
}

// §6.21 bars a nonblocking assignment to an automatic variable wherever the
// procedural block holding it stands, a generate block included (§27.3).
TEST(LifetimeIntentElaboration, GenerateBlockAutoVarNonblockingReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    initial begin\n"
      "      automatic int a;\n"
      "      a <= 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 5,
                            "6.21"));
}

// The procedural continuous assignments `assign` and `force` to an automatic
// variable are barred in a generate-for block's initial as they are in the
// module's, and a blocking assignment to it is not.
TEST(LifetimeIntentElaboration, GenerateForAutoVarProcContAssignsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    initial begin\n"
      "      automatic int a;\n"
      "      assign a = 1;\n"
      "      force a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic block variable in procedural continuous "
                            "assignment",
                            5, "6.21"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic block variable in procedural continuous "
                            "assignment",
                            6, "6.21"));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  for (genvar i = 0; i < 1; i++) begin : g\n"
             "    initial begin\n"
             "      automatic int a;\n"
             "      a = 1;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
