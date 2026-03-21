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

TEST(ScopeAndLifetimeElaboration, ForLoopInInitialBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) begin\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
