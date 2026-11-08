#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstAssignElaboration, ABitSelectWriteToAParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[3] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, APartSelectWriteToAParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[7:4] = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AConcatenationWriteToAParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial {i, P} = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromATaskBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  task t;\n"
      "    P = 7;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromAFunctionBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  function int fn;\n"
      "    P = 7;\n"
      "    return P;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInsideForkIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial fork\n"
      "    P = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (P = 0; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; P = P + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, ABitSelectWriteToALocalparamIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam logic [7:0] L = 8'hFF;\n"
      "  initial L[0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'L'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AnElementWriteToAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S[0] = \"X\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAVariableThroughABitSelectIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  logic [7:0] v;\n"
             "  initial v[3] = 1'b0;\n"
             "endmodule\n"));
}

TEST(ConstAssignElaboration, APutcOnAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S.putc(0, \"X\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AnItoaOnAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S.itoa(7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, ARealtoaOnAStringLocalparamIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam string S = \"abc\";\n"
      "  initial S.realtoa(1.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, APutcOnAStringVariableIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  string s = \"abc\";\n"
             "  initial s.putc(0, \"X\");\n"
             "endmodule\n"));
}

TEST(ConstAssignElaboration, AGetcOnAStringParameterIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  parameter string S = \"abc\";\n"
             "  byte b;\n"
             "  initial b = S.getc(0);\n"
             "endmodule\n"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInABeginEndBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial begin\n"
      "    P = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAnIfBranchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial if (i == 0) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAnElseBranchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial if (i == 0) i = 1; else P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAWhileBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial while (i < 2) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; i = i + 1) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInACaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial\n"
      "    case (i)\n"
      "      0: P = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            6, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial randcase 1: P = 1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  logic ok;\n"
      "  initial assert (ok) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  logic ok;\n"
      "  initial assert (ok) else P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { P = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            5, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 1 { P = 1; };\n"
      "      a : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            6, "6.20"));
}

struct ConstantWrite {
  const char* where;
  const char* src;
  const char* message;
  uint32_t line;
};

TEST(ConstAssignElaboration, AWriteToAConstantIsReportedInEveryFormAndPlace) {
  const ConstantWrite kWrites[] = {
      {"a const declared in a function",
       "module m;\n  function void f();\n    const static int c = 1;\n    c = "
       "5;\n"
       "  endfunction\nendmodule\n",
       "assignment to constant 'c'", 4},
      {"a const declared in a named block",
       "module m;\n  initial begin : b\n    const static int c = 1;\n    c = "
       "5;\n"
       "  end\nendmodule\n",
       "assignment to constant 'c'", 4},
      {"a localparam declared in a task",
       "module m;\n  task t;\n    localparam int L = 1;\n    L = 2;\n"
       "  endtask\nendmodule\n",
       "assignment to constant 'L'", 4},
      {"a parameter written after the block that shadows it ends",
       "module m;\n  parameter int P = 1;\n  initial begin\n"
       "    begin int P; P = 2; end\n    P = 3;\n  end\nendmodule\n",
       "assignment to constant 'P'", 5},
      {"a post-increment statement",
       "module m;\n  parameter int P = 1;\n  initial P++;\nendmodule\n",
       "assignment to constant 'P'", 3},
      {"a pre-decrement statement",
       "module m;\n  parameter int P = 1;\n  initial --P;\nendmodule\n",
       "assignment to constant 'P'", 3},
      {"an increment as a for step",
       "module m;\n  parameter int P = 1;\n"
       "  initial for (int i = 0; i < 2; P++) ;\nendmodule\n",
       "assignment to constant 'P'", 3},
      {"an increment inside a right-hand side",
       "module m;\n  parameter int P = 1;\n  int i;\n  initial i = P++;\n"
       "endmodule\n",
       "assignment to constant 'P'", 4},
      {"a decrement inside the index of a target",
       "module m;\n  parameter int P = 1;\n  int a[4];\n  initial a[P--] = 0;\n"
       "endmodule\n",
       "assignment to constant 'P'", 4},
      {"a compound assignment expression in a condition",
       "module m;\n  parameter int P = 1;\n  initial if ((P += 1) > 0) ;\n"
       "endmodule\n",
       "assignment to constant 'P'", 3},
      {"an assignment expression on a right-hand side",
       "module m;\n  parameter int P = 1;\n  int i;\n  initial i = (P = 2);\n"
       "endmodule\n",
       "assignment to constant 'P'", 4},
      {"a member of a const struct",
       "module m;\n  typedef struct { int a; } s_t;\n"
       "  const s_t s = '{a: 1};\n  initial s.a = 2;\nendmodule\n",
       "assignment to constant 's'", 4},
      {"a member of a struct parameter",
       "module m;\n  typedef struct { int a; } s_t;\n"
       "  parameter s_t P = '{a: 1};\n  initial P.a = 2;\nendmodule\n",
       "assignment to constant 'P'", 4},
      {"an output argument of a task",
       "module m;\n  parameter int P = 1;\n"
       "  task t(output int o); o = 1; endtask\n  initial t(P);\nendmodule\n",
       "constant 'P' cannot be the actual of output argument 'o' of 't'", 4},
      {"an inout argument of a task",
       "module m;\n  parameter int P = 1;\n"
       "  task t(inout int o); o = 1; endtask\n  initial t(P);\nendmodule\n",
       "constant 'P' cannot be the actual of inout argument 'o' of 't'", 4},
      {"a ref argument of a task",
       "module m;\n  parameter int P = 1;\n"
       "  task automatic t(ref int o); o = 1; endtask\n  initial t(P);\n"
       "endmodule\n",
       "constant 'P' cannot be the actual of ref argument 'o' of 't'", 4},
      {"an output argument bound by name",
       "module m;\n  parameter int P = 1;\n"
       "  task t(input int i, output int o); o = i; endtask\n"
       "  initial t(.o(P), .i(1));\nendmodule\n",
       "constant 'P' cannot be the actual of output argument 'o' of 't'", 4},
      {"an output argument of a function called in an expression",
       "module m;\n  parameter int P = 1;\n  int i;\n"
       "  function int f(output int o); o = 1; return 0; endfunction\n"
       "  initial i = f(P);\nendmodule\n",
       "constant 'P' cannot be the actual of output argument 'o' of 'f'", 5},
      {"an output argument of an imported DPI task",
       "module m;\n  parameter int P = 1;\n"
       "  import \"DPI-C\" task dt(output int o);\n  initial dt(P);\n"
       "endmodule\n",
       "constant 'P' cannot be the actual of output argument 'o' of 'dt'", 4},
      {"a const variable as an output argument",
       "module m;\n  const int c = 1;\n"
       "  task t(output int o); o = 1; endtask\n  initial t(c);\nendmodule\n",
       "constant 'c' cannot be the actual of output argument 'o' of 't'", 4},
      {"a value parameter of a class, from its method",
       "module m;\n  class C #(int N = 1);\n    function void f();\n"
       "      N = 2;\n    endfunction\n  endclass\nendmodule\n",
       "assignment to constant 'N'", 4},
      {"a localparam of a class body, from its method",
       "module m;\n  class C;\n    localparam int L = 1;\n"
       "    function void f();\n      L = 2;\n    endfunction\n  endclass\n"
       "endmodule\n",
       "assignment to constant 'L'", 5},
      {"a localparam of a class, from an out-of-block method",
       "class C;\n  localparam int L = 1;\n  extern function void f();\n"
       "endclass\nfunction void C::f();\n  L = 2;\nendfunction\nmodule m;\n"
       "endmodule\n",
       "assignment to constant 'L'", 6},
      {"a localparam of a class in a package",
       "package p;\n  class C;\n    localparam int L = 1;\n"
       "    function void f();\n      L = 2;\n    endfunction\n  endclass\n"
       "endpackage\nmodule m;\nendmodule\n",
       "assignment to constant 'L'", 5},
      {"a parameter of a package, from its function",
       "package p;\n  parameter int P = 1;\n  function void f();\n    P = 2;\n"
       "  endfunction\nendpackage\nmodule m;\nendmodule\n",
       "assignment to constant 'P'", 4},
      {"a compilation-unit parameter, from a module",
       "parameter int G = 1;\nmodule m;\n  initial G = 2;\nendmodule\n",
       "assignment to constant 'G'", 3},
      {"a compilation-unit parameter, from a compilation-unit function",
       "parameter int G = 1;\nfunction void f();\n  G = 2;\nendfunction\n"
       "module m;\nendmodule\n",
       "assignment to constant 'G'", 3},
      {"a parameter of an interface",
       "interface i;\n  parameter int P = 1;\n  initial P = 2;\nendinterface\n"
       "module m;\n  i u();\nendmodule\n",
       "assignment to constant 'P'", 3},
      {"a parameter of a program",
       "program p;\n  parameter int P = 1;\n  initial P = 2;\nendprogram\n"
       "module m;\n  p u();\nendmodule\n",
       "assignment to constant 'P'", 3},
      {"a child instance's parameter, by a hierarchical name",
       "module c #(parameter int P = 1);\nendmodule\nmodule m;\n  c u();\n"
       "  initial u.P = 2;\nendmodule\n",
       "assignment to constant 'u.P'", 5},
      {"a child instance's specify-block specparam, by a hierarchical name",
       "module c;\n  specify\n    specparam tsp = 1;\n  endspecify\n"
       "endmodule\nmodule m;\n  c u();\n  initial u.tsp = 2;\nendmodule\n",
       "assignment to constant 'u.tsp'", 8},
      {"an interface's parameter, through an interface port",
       "interface i;\n  parameter int P = 1;\nendinterface\n"
       "module c(i ifc);\n  initial ifc.P = 2;\nendmodule\nmodule m;\n"
       "  i u();\n  c v(u);\nendmodule\n",
       "assignment to constant 'ifc.P'", 5},
      {"a module's own parameter, by a name from $root",
       "module m;\n  parameter int P = 1;\n  initial $root.m.P = 2;\n"
       "endmodule\n",
       "assignment to constant '$root.m.P'", 3},
      {"a member of a compilation-unit const struct, by $unit",
       "typedef struct { int a; } s_t;\nconst s_t S = '{a: 1};\nmodule m;\n"
       "  initial $unit::S.a = 2;\nendmodule\n",
       "assignment to constant '$unit::S'", 4},
      {"a module's own parameter, by an upward name",
       "module m;\n  parameter int P = 1;\n  initial m.P = 2;\nendmodule\n",
       "assignment to constant 'm.P'", 3},
      {"a grandchild instance's localparam, by a hierarchical name",
       "module d;\n  localparam int L = 1;\nendmodule\nmodule c;\n  d v();\n"
       "endmodule\nmodule m;\n  c u();\n  initial u.v.L = 2;\nendmodule\n",
       "assignment to constant 'u.v.L'", 9},
      {"a package parameter, by a scope resolution",
       "package p;\n  parameter int P = 1;\nendpackage\nmodule m;\n"
       "  initial p::P = 2;\nendmodule\n",
       "assignment to constant 'p::P'", 5},
      {"a package parameter, through a wildcard import",
       "package p;\n  parameter int P = 1;\nendpackage\nmodule m;\n"
       "  import p::*;\n  initial P = 2;\nendmodule\n",
       "assignment to constant 'P'", 6},
      {"a package parameter, through an explicit import",
       "package p;\n  parameter int P = 1;\nendpackage\nmodule m;\n"
       "  import p::P;\n  initial P = 2;\nendmodule\n",
       "assignment to constant 'P'", 6},
      {"a compilation-unit parameter, by $unit",
       "parameter int G = 1;\nmodule m;\n  initial $unit::G = 2;\n"
       "endmodule\n",
       "assignment to constant '$unit::G'", 3},
      {"a class localparam, by a class scope resolution",
       "class C;\n  localparam int L = 1;\nendclass\nmodule m;\n"
       "  initial C::L = 2;\nendmodule\n",
       "assignment to constant 'C::L'", 5},
      {"a localparam, from a generate else branch",
       "module m;\n  localparam int P = 1;\n  if (0) begin : a\n"
       "  end else begin : b\n    initial P = 2;\n  end\nendmodule\n",
       "assignment to constant 'P'", 5},
      {"a class localparam, by the scope of a class in the module",
       "module m;\n  class C;\n    localparam int L = 1;\n  endclass\n"
       "  initial C::L = 2;\nendmodule\n",
       "assignment to constant 'C::L'", 5},
      {"a class value parameter, by its own class's scope",
       "module m;\n  class C #(parameter int N = 1);\n    function void f();\n"
       "      C::N = 2;\n    endfunction\n  endclass\nendmodule\n",
       "assignment to constant 'C::N'", 4},
      {"a base class's localparam, from a derived class's method",
       "module m;\n  class B;\n    localparam int L = 1;\n  endclass\n"
       "  class D extends B;\n    function void f();\n      L = 2;\n"
       "    endfunction\n  endclass\nendmodule\n",
       "assignment to constant 'L'", 7},
      {"a genvar inside its loop's generate block",
       "module m;\n  for (genvar i = 0; i < 2; i++) begin : g\n"
       "    initial i = 1;\n  end\nendmodule\n",
       "assignment to constant 'i'", 3},
  };
  for (const ConstantWrite& write : kWrites) {
    SCOPED_TRACE(write.where);
    ElabFixture f;
    ElaborateSrc(write.src, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), write.message, write.line, "6.20"));
  }
}

TEST(ConstAssignElaboration,
     EveryCompoundAssignmentIsReportedOnAConstantAndAcceptedOnAVariable) {
  for (const char* op : {"+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=",
                         ">>=", "<<<=", ">>>="}) {
    SCOPED_TRACE(op);
    ElabFixture f;
    ElaborateSrc(
        std::string("module m;\n  parameter int P = 1;\n  initial P ") + op +
            " 1;\nendmodule\n",
        f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "assignment to constant 'P'", 3, "6.20"));
    EXPECT_TRUE(ElabOk(std::string("module m;\n  int i;\n  initial i ") + op +
                       " 1;\nendmodule\n"));
  }
}

TEST(ConstAssignElaboration, AWriteToAConstantInsideAGenerateBlockIsReported) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "localparam int P = 1;", "initial P = 2;"},
      "assignment to constant 'P'", "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAVariableInsideAGenerateBlockIsAccepted) {
  EXPECT_TRUE(AcceptedInsideGenerateBlocks({"", "int v;", "initial v = 2;"}));
}

TEST(ConstAssignElaboration,
     AWriteToAVariableOrAShadowingDeclarationIsAccepted) {
  const char* const kAccepted[] = {
      "module m;\n  parameter int P = 1;\n  function void f();\n    int P;\n"
      "    P = 5;\n  endfunction\nendmodule\n",
      "module m;\n  parameter int P = 1;\n  task t(output int P);\n    P = 5;\n"
      "  endtask\nendmodule\n",
      "module m;\n  parameter int P = 1;\n  initial begin\n    int P;\n"
      "    P = 2;\n    P++;\n  end\nendmodule\n",
      "module m;\n  parameter int P = 1;\n"
      "  initial for (int P = 0; P < 2; P++) ;\nendmodule\n",
      "module m;\n  int c;\n  initial begin : a\n    const static int c = 1;\n "
      " end\n"
      "  initial c = 5;\nendmodule\n",
      "module m;\n  parameter int P = 1;\n  int i;\n  initial begin\n"
      "    i = P + 1;\n    i++;\n    --i;\n    i += P;\n    i = (i = P);\n"
      "  end\nendmodule\n",
      "module m;\n  typedef struct { int a; } s_t;\n  s_t s;\n"
      "  initial s.a = 2;\nendmodule\n",
      "module m;\n  parameter int P = 1;\n  const int c = 1;\n  int v;\n"
      "  task t(input int i, output int o); o = i; endtask\n"
      "  task automatic r(const ref int o); endtask\n  initial begin\n"
      "    t(P, v);\n    t(.i(c), .o(v));\n    r(c);\n  end\nendmodule\n",
      "module m;\n  parameter int P = 1;\n  class C #(int N = 1);\n    int P;\n"
      "    function void f(int N);\n      N = 2;\n      P = 3;\n"
      "    endfunction\n  endclass\nendmodule\n",
      "module m;\n  parameter int P = 1;\n  if (1) begin : g\n    int P;\n"
      "    initial P = 2;\n  end\nendmodule\n",
      "module m;\n  for (genvar i = 0; i < 2; i++) begin : g\n    int j;\n"
      "    initial j = i;\n  end\nendmodule\n",
      "module c;\n  int v;\nendmodule\nmodule m;\n  c u();\n"
      "  initial u.v = 2;\nendmodule\n",
      "package p;\n  int v;\n  function void f();\n    v = 2;\n"
      "  endfunction\nendpackage\nmodule m;\n  initial p::v = 2;\nendmodule\n",
      "package p;\n  parameter int P = 1;\nendpackage\nmodule m;\n"
      "  import p::*;\n  int P;\n  initial P = 2;\nendmodule\n",
      "interface i;\n  int v;\n  initial v = 2;\nendinterface\nmodule m;\n"
      "  i u();\nendmodule\n",
      "parameter int G = 1;\nmodule m;\n  int G;\n  initial G = 2;\n"
      "endmodule\n",
      "module m;\n  parameter int N = 1;\n  class B;\n    int N;\n"
      "  endclass\n  class D extends B;\n    function void f();\n"
      "      N = 2;\n    endfunction\n  endclass\nendmodule\n",
      "module c;\n  typedef struct { int a; } s_t;\n  s_t s;\n  s_t t[2];\n"
      "endmodule\nmodule m;\n  c u();\n  initial begin\n    u.s.a = 2;\n"
      "    u.t[0].a = 3;\n  end\nendmodule\n",
  };
  for (const char* src : kAccepted) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    for (const Diagnostic& diag : f.diag.Diagnostics()) {
      if (diag.severity == DiagSeverity::kError)
        ADD_FAILURE() << "line " << diag.loc.line << ": " << diag.message;
    }
  }
}

}  // namespace
