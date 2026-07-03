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

TEST(SubroutineCallElaboration, VoidFunctionAsOperandError) {
  // Only a nonvoid function call may appear as an operand within an
  // expression; using a void function call as an operand is illegal.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd1;\n"
      "  endfunction\n"
      "  initial x = set_x() + 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgConcatenationOk) {
  // §13.5: an output actual may be any expression valid as a procedural-
  // assignment lvalue (§10.4). A concatenation of variables is such an lvalue,
  // so binding it to an output formal must elaborate without error.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  function void get(output logic [7:0] o);\n"
      "    o = 8'hAB;\n"
      "  endfunction\n"
      "  initial get({a, b});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgConcatenationWithLiteralError) {
  // A concatenation is a valid lvalue only when every element is assignable;
  // a literal element cannot appear on the left of a procedural assignment, so
  // the concatenation is not a valid output actual.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  function void get(output logic [7:0] o);\n"
      "    o = 8'hAB;\n"
      "  endfunction\n"
      "  initial get({a, 4'd5});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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

TEST(SubroutineCallElaboration, OutputArgPartSelectOk) {
  // §13.5/§10.4: a part-select is a valid procedural-assignment lvalue, so it
  // is an admissible output actual (a distinct syntactic form from a scalar
  // bit-select).
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void get(output logic [3:0] v);\n"
      "    v = 4'd1;\n"
      "  endfunction\n"
      "  initial get(x[3:0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgMemberSelectOk) {
  // A member select of a packed struct is a valid procedural-assignment lvalue
  // (§10.4) and is therefore an admissible output actual.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  function void get(output logic [3:0] v);\n"
      "    v = 4'd1;\n"
      "  endfunction\n"
      "  initial get(s.lo);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, InoutArgSelectOk) {
  // The lvalue restriction applies equally to the inout direction: an element
  // select of an unpacked array is a valid inout actual.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  function void bump(inout logic [7:0] io);\n"
      "    io = io + 8'd1;\n"
      "  endfunction\n"
      "  initial bump(arr[0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
