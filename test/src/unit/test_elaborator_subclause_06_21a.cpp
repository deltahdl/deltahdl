#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ScopeAndLifetimeElaboration, ModuleLevelVarStaticLifetime) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int st0;\n"
      "  initial st0 = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ScopeAndLifetimeElaboration, StaticVarInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  initial begin\n"
      "    static int counter = 0;\n"
      "    counter = counter + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ScopeAndLifetimeElaboration, StaticVarInAutoFunc) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function automatic int accum(int x);\n"
      "    static int sum = 0;\n"
      "    sum = sum + x;\n"
      "    return sum;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ScopeAndLifetimeElaboration, AutoVarInStaticFunc) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function static int process(int x);\n"
      "    automatic int temp = x + 1;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ScopeAndLifetimeElaboration, ModuleAutomaticLifetime) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module automatic top;\n"
      "  function int foo(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ScopeAndLifetimeElaboration, LocalScopesDoNotConflict) {
  EXPECT_TRUE(
      ElabOk("module a; logic x; endmodule\n"
             "module b; logic x; endmodule\n"));
}

TEST(ScopeAndLifetimeElaboration, LifetimeStaticElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  static int x = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, LifetimeAutomaticElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  initial begin\n"
      "    automatic int y = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, AutomaticInModuleScopeError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  automatic int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic lifetime is not allowed on module-level variables", 2,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, AutomaticVarForceInTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    force x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic task variable in procedural continuous assignment", 4,
      "13.3.2"));
}

TEST(ScopeAndLifetimeElaboration, AutomaticVarProceduralAssignInTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    assign x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic task variable in procedural continuous assignment", 4,
      "13.3.2"));
}

TEST(ScopeAndLifetimeElaboration, StaticVarForceInTaskSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    static int x;\n"
      "    force x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, StaticTaskAutoVarNonblockingIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module nba_holder;\n"
      "  task static drive();\n"
      "    automatic int pulse;\n"
      "    pulse <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 4,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration,
     StaticTaskAutoVarNonblockingEventControlIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module evc_holder;\n"
      "  logic ready;\n"
      "  task static sync();\n"
      "    automatic int gate;\n"
      "    ready <= @(gate) 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in intra-assignment event "
                            "control of nonblocking assignment",
                            5, "6.21"));
}

TEST(ScopeAndLifetimeElaboration, StaticTaskAutoVarMonitorIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module mon_holder;\n"
      "  task static probe();\n"
      "    automatic int sample;\n"
      "    $monitor(\"%d\", sample);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable traced by system task", 4,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration, StaticTaskAutoVarForceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module frc_holder;\n"
      "  task static hold();\n"
      "    automatic int level;\n"
      "    force level = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in procedural continuous "
                            "assignment",
                            4, "6.21"));
}

TEST(ScopeAndLifetimeElaboration, StaticTaskAutoVarProcAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module pca_holder;\n"
      "  task static latch_it();\n"
      "    automatic int keep;\n"
      "    assign keep = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in procedural continuous "
                            "assignment",
                            4, "6.21"));
}

TEST(ScopeAndLifetimeElaboration, StaticTaskDefaultLifetimeVarNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dfl_holder;\n"
      "  task static bump();\n"
      "    int total;\n"
      "    total <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, AutoVarNonblockingInInitialIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 4,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration, AutoVarForceInInitialIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    force x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic block variable in procedural continuous assignment", 4,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, AutoVarProcAssignInAlwaysIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  always @(posedge clk) begin\n"
      "    automatic int x;\n"
      "    assign x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic block variable in procedural continuous assignment", 5,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, StaticVarNonblockingInInitialOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    static int x;\n"
      "    x <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, FunctionDeclLifetimeAutomatic) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function automatic int f(); return 0; endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  EXPECT_TRUE(mod->function_decls[0]->is_automatic);
}

TEST(ScopeAndLifetimeElaboration, FunctionDeclLifetimeStatic) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function static int f(); return 0; endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  EXPECT_TRUE(mod->function_decls[0]->is_static);
}

TEST(ScopeAndLifetimeElaboration, TaskDeclLifetimeAutomatic) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic my_task;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  EXPECT_TRUE(mod->function_decls[0]->is_automatic);
}

TEST(ScopeAndLifetimeElaboration, TaskDeclLifetimeStatic) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task static my_task;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  EXPECT_TRUE(mod->function_decls[0]->is_static);
}

TEST(ScopeAndLifetimeElaboration, DynamicArrayElementNonblockingIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[] = new[4];\n"
      "  initial d[0] <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 3,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, DynamicArrayElementForceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[] = new[4];\n"
      "  initial force d[0] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "procedural continuous assignment to element of dynamic array", 3,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, DynamicArrayElementProcAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[] = new[4];\n"
      "  initial assign d[0] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "procedural continuous assignment to element of dynamic array", 3,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, StaticVarInAutoTask) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic work();\n"
      "    static int count = 0;\n"
      "    count = count + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, AutoVarInStaticTask) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static work();\n"
      "    automatic int temp = 0;\n"
      "    temp = temp + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, DefaultLifetimeTask) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task my_task(input int n);\n"
      "    $display(\"%0d\", n);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, AutoVarInAutoTask) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic work();\n"
      "    automatic int temp = 0;\n"
      "    temp = temp + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, StaticVarInStaticTask) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static work();\n"
      "    static int count = 0;\n"
      "    count = count + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, ClassMethodDefaultsAutomatic) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function int f(); return 0; endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->cu_class_decls.empty());
  auto* cls = design->cu_class_decls[0];
  ASSERT_FALSE(cls->members.empty());
  ASSERT_NE(cls->members[0]->method, nullptr);
  EXPECT_TRUE(cls->members[0]->method->is_automatic);
}

TEST(ScopeAndLifetimeElaboration,
     ClassMethodDefaultsAutomaticInsideStaticModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    function int f(); return 0; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->class_decls.empty());
  auto* cls = mod->class_decls[0];
  ASSERT_FALSE(cls->members.empty());
  ASSERT_NE(cls->members[0]->method, nullptr);
  EXPECT_TRUE(cls->members[0]->method->is_automatic);
}

TEST(ScopeAndLifetimeElaboration, ForLoopVariableDefaultsAutomaticElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      automatic int local_val = i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration,
     NonblockingAssignToDynamicArrayElementInARandcaseArmIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[] = new[4];\n"
      "  initial randcase\n"
      "    1 : d[0] <= 1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 4,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration,
     NonblockingAssignToAWholeDynamicArrayInARandcaseArmIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d[] = new[4];\n"
      "  int e[] = new[4];\n"
      "  initial randcase\n"
      "    1 : d <= e;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration,
     AutoVarDeclaredInAForkIsReachedByTheNonblockingRule) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      automatic int x;\n"
      "      x <= 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 5,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration,
     AutoVarNonblockingInAnAssertionPassStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    assert (1) begin\n"
      "      automatic int x;\n"
      "      x <= 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 5,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration,
     AutoVarNonblockingInAnAssertionFailStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    assert (1) else begin\n"
      "      automatic int x;\n"
      "      x <= 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 5,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration, AutoVarNonblockingInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : begin\n"
      "        automatic int x;\n"
      "        x <= 1;\n"
      "      end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 6,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration,
     AutoVarNonblockingInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { automatic int x; x <= 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 4,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration,
     AutoVarNonblockingInARandsequenceWeightCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { automatic int x; x <= 1; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 4,
                            "6.21"));
}

TEST(ScopeAndLifetimeElaboration, BlockScopedQueueElementNonblockingIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int q[$];\n"
      "    q.push_back(0);\n"
      "    q[0] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 5,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, BlockScopedAssocElementNonblockingIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int aa[int];\n"
      "    aa[5] = 0;\n"
      "    aa[5] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 5,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, TaskScopedDynamicArrayElementNbaIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t1();\n"
      "    int d[];\n"
      "    d = new[2];\n"
      "    d[0] <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 5,
      "6.21"));
}

TEST(ScopeAndLifetimeElaboration, BlockScopedFixedArrayElementNbaIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int a[0:3];\n"
      "    a[0] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ScopeAndLifetimeElaboration, BlockScopedParamSizedArrayElementNbaIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  initial begin\n"
      "    int a[N];\n"
      "    a[0] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ScopeAndLifetimeElaboration,
     GenerateScopedQueueElementNonblockingIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter P = 3;\n"
      "  generate\n"
      "    if (P == 1) begin : t1\n"
      "      int qa[$];\n"
      "      initial qa[0] <= 1;\n"
      "    end else begin : t2\n"
      "      int qb[$];\n"
      "      initial qb[0] <= 1;\n"
      "    end\n"
      "    case (P)\n"
      "      1: begin : c1\n"
      "        int qc[$];\n"
      "        initial qc[0] <= 1;\n"
      "      end\n"
      "      default: begin : c2\n"
      "        int qd[$];\n"
      "        initial qd[0] <= 1;\n"
      "      end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 9,
      "6.21"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "nonblocking assignment to element of dynamically sized array", 18,
      "6.21"));
}

}  // namespace
