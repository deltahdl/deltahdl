#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprElaboration, MethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function void method(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, SystemCallStatementElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TfCallNoArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial t();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TfCallWithPositionalArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = f(1, 2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ConstantFunctionCallInParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a); return a + 1; endfunction\n"
      "  parameter P = f(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, SystemTfCallBareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, NamedArgumentsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b); return a - b; endfunction\n"
      "  int x;\n"
      "  initial x = f(.a(10), .b(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, MixedPositionalAndNamedArgsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b, int c); return a + b + c; endfunction\n"
      "  int x;\n"
      "  initial x = f(1, 2, .c(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, RandomizeBasicElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TaskCallWithoutParensElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, VoidFunctionCallWithoutParensElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void log; endfunction\n"
      "  initial log;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, NonVoidFunctionCallWithoutParensRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f; return 1; endfunction\n"
      "  initial f;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot omit parentheses in call to nonvoid function 'f'", 3, "13.5.5"));
}

TEST(SubroutineCallExprElaboration, ScopeRandomizeWithNullRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration, StdRandomizeWithNullRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin std::randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration, ScopeRandomizeWithParenIdListRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope randomize call cannot use a parenthesized "
                            "identifier list after 'with'",
                            2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ClassMethodRandomizeWithParenIdListAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
      "  initial begin obj.randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ConstantFunctionCallWithParameterArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int B = 41;\n"
      "  function int inc(int n); return n + 1; endfunction\n"
      "  localparam int P = inc(B);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ConstantFunctionCallWithLocalparamArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int B = 41;\n"
      "  function int inc(int n); return n + 1; endfunction\n"
      "  localparam int P = inc(B);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ScopeRandomizeWithNullInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial fork\n"
      "    randomize(null);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 3, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial assert (1) randomize(null);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial assert (1) else randomize(null);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial randcase\n"
      "    1 : randomize(null);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 3, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { randomize(null); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 4, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInRandsequenceWeightCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { randomize(null); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 5, "A.8.2"));
}

TEST(SubroutineCallElaborationSyntax, ACallNamingAVariableOrANetIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  wire w;\n"
      "  int y;\n"
      "  initial begin\n"
      "    x;\n"
      "    y = x(1);\n"
      "    w();\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "' names a variable or a net, and a call names a task or a function";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'x") + kMessage,
                            6, "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'x") + kMessage,
                            7, "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'w") + kMessage,
                            8, "A.8.2"));
}

TEST(SubroutineCallElaborationSyntax,
     ACallAttachedToASequenceNamingDataIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic clk, a, b);\n"
      "  int count;\n"
      "  wire w;\n"
      "  task tick; endtask\n"
      "  sequence s1; @(posedge clk) (a, count) ##1 b; endsequence\n"
      "  sequence s2; @(posedge clk) (a, count()) ##1 b; endsequence\n"
      "  sequence s3; int v; @(posedge clk) (a, v = 1, v) ##1 b; endsequence\n"
      "  sequence s4; @(posedge clk) (a, tick) ##1 b; endsequence\n"
      "  sequence s5(q); @(posedge clk) (a, q) ##1 b; endsequence\n"
      "  sequence s6(count); @(posedge clk) (a, count) ##1 b; endsequence\n"
      "  sequence s7; @(posedge clk) first_match(a ##1 b, count); endsequence\n"
      "  property p1; @(posedge clk) (a, w) |-> b; endproperty\n"
      "  property p2; int v; @(posedge clk) (a, v = 1, v) |-> b; endproperty\n"
      "  a1: assert property (@(posedge clk) (a, count) |-> b);\n"
      "  c1: cover sequence (@(posedge clk) (a, count) ##1 b);\n"
      "  initial begin a2: assert property (@(posedge clk) (a, count) |-> b); "
      "end\n"
      "endmodule\n",
      f);
  const std::string kMessage =
      "' names a variable or a net, and a call names a task or a function";
  for (const auto& [name, line] :
       std::initializer_list<std::pair<const char*, uint32_t>>{{"count", 5},
                                                               {"count", 6},
                                                               {"v", 7},
                                                               {"count", 11},
                                                               {"w", 12},
                                                               {"v", 13},
                                                               {"count", 14},
                                                               {"count", 15},
                                                               {"count", 16}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("'") + name + kMessage, line,
                              "A.8.2"))
        << "line " << line;
  }
  for (const auto& [name, line] :
       std::initializer_list<std::pair<const char*, uint32_t>>{
           {"tick", 8}, {"q", 9}, {"count", 10}}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               std::string("'") + name + kMessage, line,
                               "A.8.2"))
        << "line " << line;
  }
}

TEST(SubroutineCallElaborationSyntax, ACallOfATaskOrFunctionIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; function void g(); endfunction endclass\n"
      "module m;\n"
      "  task t; endtask\n"
      "  function int fn(); return 1; endfunction\n"
      "  C c, d;\n"
      "  int y;\n"
      "  initial begin\n"
      "    if (y == 0) t; else t();\n"
      "    c = new;\n"
      "    d = new c;\n"
      "    c.g();\n"
      "    y = fn();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, ACallNamingABlocksVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int g(); return 1; endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    begin int g; g; end\n"
      "    fork int z; z(); join\n"
      "    y = g();\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "' names a variable or a net, and a call names a task or a function";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'g") + kMessage,
                            5, "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'z") + kMessage,
                            6, "A.8.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), std::string("'g") + kMessage,
                             7, "A.8.2"));
}

TEST(SubroutineCallElaborationSyntax,
     ACallStatementNamingNoSubroutineIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package q; int u; endpackage\n"
      "package p; int v; int w; function void pf(); endfunction endpackage\n"
      "module m;\n"
      "  import p::v;\n"
      "  import q::*;\n"
      "  let l(a) = a;\n"
      "  sequence s; 1; endsequence\n"
      "  property pr; 1; endproperty\n"
      "  int y;\n"
      "  initial begin\n"
      "    l(1);\n"
      "    s;\n"
      "    pr;\n"
      "    v;\n"
      "    u;\n"
      "    y = l(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "' names no task or function, and a call statement calls one";
  for (const auto& [name, line] : {std::pair<const char*, uint32_t>{"l", 11},
                                   {"s", 12},
                                   {"pr", 13},
                                   {"v", 14},
                                   {"u", 15}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("'") + name + kMessage, line,
                              "A.6.9"))
        << name;
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), std::string("'l") + kMessage,
                             16, "A.6.9"));
}

TEST(SubroutineCallElaborationSyntax, ACallStatementNamesASubroutine) {
  ElabFixture f;
  ElaborateSrc(
      "package q; int qv; task qt; endtask endpackage\n"
      "package p; function void pf(); endfunction task pt; endtask\n"
      "endpackage\n"
      "import q::*;\n"
      "function void uf(); endfunction\n"
      "module m;\n"
      "  import p::pf;\n"
      "  parameter int P = 1;\n"
      "  import \"DPI-C\" function void cf();\n"
      "  function void fe(); endfunction\n"
      "  export \"DPI-C\" function fe;\n"
      "  task t; endtask\n"
      "  int x;\n"
      "  initial begin\n"
      "    P;\n"
      "    P();\n"
      "    if (0) begin uf(); pf(); qt; t; cf(); fe(); randomize(x); end\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "' names no task or function, and a call statement calls one";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'P") + kMessage,
                            15, "A.6.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'P") + kMessage,
                            16, "A.6.9"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 17u) << diag.message;
  }
}

TEST(SubroutineCallElaborationSyntax, ACallNamingAUnitVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "int g;\n"
      "wire w;\n"
      "int h;\n"
      "int q;\n"
      "module m;\n"
      "  task h(int a); endtask\n"
      "  parameter int q = 1;\n"
      "  int y;\n"
      "  initial begin\n"
      "    g(1);\n"
      "    y = w(1);\n"
      "    h(1);\n"
      "    q(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kData =
      "' names a variable or a net, and a call names a task or a function";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'g") + kData, 10,
                            "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'w") + kData, 11,
                            "A.8.2"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'q' names no task or function, and a call statement calls one", 13,
      "A.6.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), std::string("'q") + kData,
                             13, "A.8.2"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 12u) << diag.message;
  }
}

TEST(SubroutineCallElaborationSyntax, AForStepNamingDataIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int i;\n"
      "  function void bump(); i++; endfunction\n"
      "  task tick; endtask\n"
      "  initial begin\n"
      "    for (i = 0; i < 4; i) ;\n"
      "    for (i = 0; i < 4; bump) ;\n"
      "    for (i = 0; i < 4; tick) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'i' names a variable or a net, and a call names "
                            "a task or a function",
                            6, "A.8.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(SubroutineCallElaborationSyntax, ANonvoidFunctionCallKeepsItsParentheses) {
  ElabFixture f;
  ElaborateSrc(
      "package q; task qt; endtask endpackage\n"
      "package p;\n"
      "  function int g(); return 2; endfunction\n"
      "  function void w(); endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  function void v(); endfunction\n"
      "  task t; endtask\n"
      "  initial begin\n"
      "    f;\n"
      "    p::g;\n"
      "    f();\n"
      "    v;\n"
      "    t;\n"
      "    p::w;\n"
      "    q::qt;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to nonvoid "
                            "function 'f'",
                            11, "13.5.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to nonvoid "
                            "function 'p::g'",
                            12, "13.5.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(SubroutineCallElaborationSyntax, AVoidCastOfANameAloneIsJudgedAsACall) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    function int get(); return x; endfunction\n"
      "    function void touch(); void'(get); endfunction\n"
      "  endclass\n"
      "  int i;\n"
      "  function int f(); return 1; endfunction\n"
      "  C obj = new;\n"
      "  initial begin\n"
      "    void'(i);\n"
      "    void'(f);\n"
      "    void'(obj.get);\n"
      "    void'(obj.randomize);\n"
      "    void'(f());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'i' names a variable or a net, and a call names "
                            "a task or a function",
                            11, "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to nonvoid "
                            "function 'f'",
                            12, "13.5.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
