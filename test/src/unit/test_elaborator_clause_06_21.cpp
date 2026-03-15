#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, ModuleLevelVarStaticLifetime) {
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

TEST(Elaboration, StaticVarInInitialBlock) {
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

TEST(Elaboration, AutomaticVarInInitialBlock) {
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

TEST(Elaboration, StaticVarInAutoFunc) {
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

TEST(Elaboration, AutoVarInStaticFunc) {
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

TEST(Elaboration, ModuleAutomaticLifetime) {
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

TEST(ModuleScope, LocalScopesDoNotConflict) {
  EXPECT_TRUE(
      ElabOk("module a; logic x; endmodule\n"
             "module b; logic x; endmodule\n"));
}

}  // namespace
