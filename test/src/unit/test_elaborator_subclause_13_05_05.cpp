#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineCallElaborationSyntax, TaskCallWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd1;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidFunctionWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd1;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, NonvoidFunctionWithoutParensError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int get_val; return 1; endfunction\n"
      "  initial get_val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax,
     NonvoidFunctionAllDefaultsWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int get_val(int v = 1); return v; endfunction\n"
      "  initial get_val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, TaskAllDefaultsWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x(int v = 42);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax,
     VoidFunctionAllDefaultsWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x(int v = 42);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidClassMethodNoArgsWithoutParensOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function void touch; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new();\n"
      "  initial c.touch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, ClassMethodAllDefaultsWithoutParensOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function void take(int v = 1); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new();\n"
      "  initial c.take;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, TaskWithRequiredArgWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x(int v);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax,
     VoidFunctionWithRequiredArgWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x(int v);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax,
     TaskWithMixedDefaultAndRequiredArgsWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  task compute(int a = 1, int b);\n"
      "    x = a + b;\n"
      "  endtask\n"
      "  initial compute;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax,
     NonvoidClassMethodBareNameIsNotARecursiveCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function int foo();\n"
      "    foo = 3;\n"
      "    foo;\n"
      "    return foo;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
