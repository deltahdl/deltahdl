#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 5,
                            "13.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "inout argument 'x' requires a variable", 5,
                            "13.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too many arguments to 'foo': expected 1, got 3", 4,
                            "13.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'b' in call to 'foo'", 4,
                            "13.5.3"));
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
      "class C;\n"
      "  function int method(); return 0; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'set_x' used as expression operand",
                            6, "13.4.1"));
}

TEST(SubroutineCallElaboration, OutputArgConcatenationOk) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'o' requires a variable", 6,
                            "13.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 6,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgPartSelectOk) {
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

TEST(SubroutineCallElaboration, OutputArgLiteralInForkArmError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial fork\n"
      "    foo(42);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 6,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgLiteralInAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial assert (1) foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 5,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgLiteralInAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial assert (1) else foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 5,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgLiteralInRandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial randcase\n"
      "    1 : foo(42);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 6,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgLiteralInRandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { foo(42); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 7,
                            "13.5"));
}

TEST(SubroutineCallElaboration,
     OutputArgLiteralInRandsequenceWeightCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { foo(42); };\n"
      "      alt : { y = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 8,
                            "13.5"));
}

TEST(SubroutineCallElaboration, NetAsOutputOrInoutActualError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire [3:0] wv;\n"
      "  logic v;\n"
      "  task t(output logic o); o = 1; endtask\n"
      "  function void g(inout logic [1:0] io); endfunction\n"
      "  initial begin\n"
      "    t(w);\n"
      "    g({v, wv[0]});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net 'w' cannot be the actual of output argument "
                            "'o'",
                            8, "13.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net 'wv' cannot be the actual of inout argument "
                            "'io'",
                            9, "13.5"));
}

TEST(SubroutineCallElaboration,
     DISABLED_ClassHandleActualOfAnUnrelatedClassIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "class DA extends A; endclass\n"
      "function void fb(B x); endfunction\n"
      "task tb(input B x); endtask\n"
      "function void ob(output B x); x = null; endfunction\n"
      "function automatic void rb(ref B x); endfunction\n"
      "function void fa(A x); endfunction\n"
      "function void fd(DA x); endfunction\n"
      "function automatic void ra(ref A x); endfunction\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  DA da;\n"
      "  initial begin\n"
      "    fb(a);\n"
      "    tb(a);\n"
      "    ob(a);\n"
      "    rb(a);\n"
      "    fa(da);\n"
      "    fd(a);\n"
      "    ra(da);\n"
      "    fa(a);\n"
      "    fb(b);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {16, 17, 18, 21}) {
    EXPECT_TRUE(ReportedError(diags, "assignment compatible", kLine, "13.5"))
        << kLine;
  }
  for (const int kLine : {19, 22}) {
    EXPECT_TRUE(ReportedError(diags, "equivalent", kLine, "13.5.2")) << kLine;
  }
  for (const int kLine : {20, 23, 24}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
