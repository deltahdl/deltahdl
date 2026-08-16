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
  // §6.21: a variable may be explicitly declared automatic within a procedural
  // block. (Module-level automatic is illegal and is covered separately by
  // VarDecl.AutomaticInModuleScopeError.)
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
  // The parser's §6.8 report comes first and the source does not parse; the
  // permissive helper says so, and the assertion below names the §6.21 rule.
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  automatic int x;\n"
      "endmodule\n",
      f);
  // The source draws two reports: Parser::ParseDataDeclItem rejects the
  // lifetime keyword under §6.8, and Elaborator::ElaborateVarDecl rejects the
  // module-level automatic variable under §6.21. This names the second.
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
  // The report stands under §13.3.2, not §6.21:
  // Elaborator::ValidateFunctionBody routes a task body to
  // CheckTaskBodyContAssign, which enforces the §13.3.2 sentence about
  // variables declared in automatic tasks. CheckAutoVarWritesInProc enforces a
  // different sentence, the §6.21 one about automatic variables in a procedural
  // block, and each message names the construct its own sentence is scoped to.
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
  // CheckTaskBodyContAssign again, so the §13.3.2 sentence rather than the
  // §6.21 one, and the message says "task variable" rather than "block
  // variable".
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

// §6.21 is the clause for this report, not §13.3.2. §6.21 says "Automatic
// variables and elements of dynamically sized array variables shall not be
// written with nonblocking, continuous, or procedural continuous assignments",
// and that sentence is about how a variable was declared rather than about
// which task declared it. §13.3.2's four bullets open "Because variables
// declared in automatic tasks are deallocated at the end of the task
// invocation", so they reach a variable of an automatic task only, and `drive`
// carries the `static` keyword. §13.3.1 is what makes the declaration legal
// there: "Specific local variables can be declared as automatic within a static
// task or as static within an automatic task."
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

// The sentence broken here is §6.21's last one: "References to automatic
// variables and elements or members of dynamic variables shall be limited to
// procedural blocks." An intra-assignment event control holds the reference to
// `gate` until the event fires, which is after the statement that named it has
// finished. §13.3.2 has a bullet for the same construct, "They shall not be
// referenced in intra-assignment event controls of nonblocking assignments",
// but its subject is a variable declared in an automatic task and `sync` is a
// static one.
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

// $monitor keeps reading its arguments for the remainder of the simulation, so
// naming `sample` in one places a reference to an automatic variable outside
// the block that declared it, which §6.21's "References to automatic variables
// ... shall be limited to procedural blocks" forbids. The citation is §6.21
// rather than §13.3.2 because `probe` is declared `task static`, and §13.3.2's
// bullet "They shall not be traced with system tasks such as $monitor and
// $dumpvars" governs variables of automatic tasks.
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

// §6.21 bars a procedural continuous assignment over an automatic variable in
// the same sentence that bars a nonblocking one, and `force` is a procedural
// continuous assignment. The message says "automatic variable" rather than
// "automatic task variable" because `level` is not a variable of an automatic
// task: `hold` is static, and §13.3.1 permits the `automatic` keyword on a
// local inside it.
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

// `assign` is the other procedural continuous assignment statement, and §6.21
// reaches it through the same sentence that reaches `force`. It is pinned apart
// from StaticTaskAutoVarForceIsError so that a change routing only one of the
// two statement kinds to the check shows up. §13.3.2's own bullet names both,
// "They shall not be referenced by assign or force procedural continuous
// assignments", and applies to neither statement here, since `latch_it` is a
// static task.
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

// §6.21 accepts this: "Variables declared inside a static task, function, or
// block are local in scope and default to a static lifetime", so `total` is
// static and no restriction on automatic variables reaches it. This is the
// input that makes the five rejections above mean something. Without it a test
// over `automatic int` passes whether the elaborator reads the declaration's
// lifetime or assumes one from the task's.
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
      "      int local_val = i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
