#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>

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

struct RejectedActual {
  const char* call;
  const char* report;
  const char* subclause;
};

constexpr RejectedActual kRejectedActuals[] = {
    {"o(g())", "output argument 'x' requires a variable", "13.5"},
    {"o($time)", "output argument 'x' requires a variable", "13.5"},
    {"o(c0 ? y : z)", "output argument 'x' requires a variable", "13.5"},
    {"o(int'(y))", "output argument 'x' requires a variable", "13.5"},
    {"o(-y)", "output argument 'x' requires a variable", "13.5"},
    {"io(g())", "inout argument 'x' requires a variable", "13.5"},
    {"io(y + z)", "inout argument 'x' requires a variable", "13.5"},
    {"o(P)", "constant 'P' cannot be the actual of output argument 'x' of 'o'",
     "6.20"},
    {"o(L)", "constant 'L' cannot be the actual of output argument 'x' of 'o'",
     "6.20"},
    {"o(K)", "constant 'K' cannot be the actual of output argument 'x' of 'o'",
     "6.20"},
    {"o(E1)",
     "constant 'E1' cannot be the actual of output argument 'x' of 'o'",
     "6.20"},
    {"io(P)", "constant 'P' cannot be the actual of inout argument 'x' of 'io'",
     "6.20"},
};

TEST(SubroutineCallElaboration,
     AnOutputOrInoutActualThatIsNoProceduralLvalueIsReportedInEveryKind) {
  for (const auto& actual : kRejectedActuals) {
    ElabFixture f;
    ElaborateSrc(std::string("module m;\n"
                             "  parameter int P = 1;\n"
                             "  localparam int L = 2;\n"
                             "  const int K = 3;\n"
                             "  typedef enum {E0, E1} e_t;\n"
                             "  int y, z;\n"
                             "  logic c0;\n"
                             "  function int g(); return 1; endfunction\n"
                             "  function void o(output int x); x = 1; "
                             "endfunction\n"
                             "  function void io(inout int x); x = 1; "
                             "endfunction\n"
                             "  initial ") +
                     actual.call +
                     ";\n"
                     "endmodule\n",
                 f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), actual.report, 11,
                              actual.subclause))
        << actual.call;
  }
}

TEST(SubroutineCallElaboration,
     AnOutputOrInoutActualThatIsAProceduralLvalueIsAcceptedInEveryKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c; int v; endmodule\n"
      "module m;\n"
      "  class H; int p; endclass\n"
      "  int a[4], d[], q[$], s[string];\n"
      "  logic [15:0] b;\n"
      "  H h = new;\n"
      "  c u();\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  function void io(inout int x); x = 1; endfunction\n"
      "  function void o8(output logic [7:0] x); x = 1; endfunction\n"
      "  initial begin\n"
      "    o(a[1]);\n"
      "    o(d[0]);\n"
      "    o(q[0]);\n"
      "    o(s[\"k\"]);\n"
      "    o(h.p);\n"
      "    o(u.v);\n"
      "    o8(b[3+:8]);\n"
      "    io(a[2]);\n"
      "    io(h.p);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

struct LiteralOutputCall {
  const char* src;
  int line;
};

constexpr LiteralOutputCall kReportedLiteralOutputCalls[] = {
    {("module m;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  task t; o(5); endtask\n"
      "endmodule\n"),
     3},
    {("module m;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  function void g; o(5); endfunction\n"
      "endmodule\n"),
     3},
    {("module m;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  class C; function void g; o(5); endfunction endclass\n"
      "endmodule\n"),
     3},
    {("interface i;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  initial o(5);\n"
      "endinterface\n"
      "module m; i u(); endmodule\n"),
     3},
    {("program q;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  initial o(5);\n"
      "endprogram\n"),
     3},
    {("module m;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  if (1) begin : b initial o(5); end\n"
      "endmodule\n"),
     3},
    {("package p;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "endpackage\n"
      "module m; import p::*; initial o(5); endmodule\n"),
     4},
};

constexpr LiteralOutputCall kUnreportedLiteralOutputCalls[] = {
    {("package p;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  function void g; o(5); endfunction\n"
      "endpackage\n"),
     3},
    {("function void o(output int x); x = 1; endfunction\n"
      "function void g; o(5); endfunction\n"),
     2},
    {("class C;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "  function void g; o(5); endfunction\n"
      "endclass\n"),
     3},
    {("package p;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "endpackage\n"
      "module m; initial p::o(5); endmodule\n"),
     4},
    {("function void o(output int x); x = 1; endfunction\n"
      "module m; initial o(5); endmodule\n"),
     2},
    {("module c;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "endmodule\n"
      "module m; c u(); initial u.o(5); endmodule\n"),
     4},
    {("class C;\n"
      "  function void o(output int x); x = 1; endfunction\n"
      "endclass\n"
      "module m; C h = new; initial h.o(5); endmodule\n"),
     4},
};

template <size_t N>
void ExpectLiteralOutputReported(const LiteralOutputCall (&calls)[N]) {
  for (const auto& call : calls) {
    ElabFixture f;
    ElaborateSrc(call.src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "output argument 'x' requires a variable",
                              call.line, "13.5"))
        << call.src;
  }
}

TEST(SubroutineCallElaboration,
     ALiteralOutputActualIsReportedInAModuleInterfaceProgramOrImport) {
  ExpectLiteralOutputReported(kReportedLiteralOutputCalls);
}

TEST(SubroutineCallElaboration,
     DISABLED_ALiteralOutputActualIsReportedInAPackageTheUnitOrAnotherScope) {
  ExpectLiteralOutputReported(kUnreportedLiteralOutputCalls);
}

}  // namespace
