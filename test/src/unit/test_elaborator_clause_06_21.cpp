#include "fixture_elaborator.h"

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

TEST(ScopeAndLifetimeElaboration, AutomaticVarInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  initial begin\n"
      "    automatic int temp = 42;\n"
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
      "  automatic int y = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, AutomaticInModuleScopeError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  automatic int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, DynamicArrayElementForceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[] = new[4];\n"
      "  initial force d[0] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ScopeAndLifetimeElaboration, DynamicArrayElementProcAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[] = new[4];\n"
      "  initial assign d[0] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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
