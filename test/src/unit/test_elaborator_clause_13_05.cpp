#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineCallElaboration, FunctionCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int foo(int a); return a + 1; endfunction\n"
      "  int x;\n"
      "  initial x = foo(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgLiteralError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaboration, InoutArgLiteralError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(inout int x);\n"
      "    x = x + 1;\n"
      "  endfunction\n"
      "  initial foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgVariableOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial foo(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, TooManyArgsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo(int a); return a; endfunction\n"
      "  int x;\n"
      "  initial x = foo(1, 2, 3);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaboration, TooFewArgsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = foo(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaboration, InoutArgVariableOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  function void foo(inout int x);\n"
      "    x = x + 1;\n"
      "  endfunction\n"
      "  initial foo(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, TaskCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd1;\n"
      "  endtask\n"
      "  initial set_x();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidCastOfMethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial void'(obj.method());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, FunctionCallReturnValueElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] get_val(); return 8'd42; endfunction\n"
      "  initial x = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgSelectOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  function void get(output logic [7:0] v);\n"
      "    v = 8'd1;\n"
      "  endfunction\n"
      "  initial get(arr[0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgBinaryExprError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a, b;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial foo(a + b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

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

}  // namespace
