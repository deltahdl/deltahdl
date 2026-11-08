#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(NameSpaceRedeclaration, TwoVariablesOfOneNameInAnInterface) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("interface i;\n"
             "  logic x;\n"
             "  logic x;\n"
             "endinterface\n"
             "module top; i u(); endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "6.5"));
}

TEST(NameSpaceRedeclaration, TwoVariablesOfOneNameInAProgram) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("program p;\n"
             "  logic x;\n"
             "  logic x;\n"
             "endprogram\n"
             "module top; p u(); endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "6.5"));
}

TEST(NameSpaceRedeclaration, TwoVariablesOfOneNameInAChecker) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("checker c;\n"
             "  bit x;\n"
             "  bit x;\n"
             "endchecker\n"
             "module top; c u(); endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "6.5"));
}

TEST(NameSpaceRedeclaration, DistinctVariablesInAnInterfaceProgramAndChecker) {
  EXPECT_TRUE(
      ElabOk("interface i;\n"
             "  logic x;\n"
             "  logic y;\n"
             "endinterface\n"
             "program p;\n"
             "  logic x;\n"
             "  logic y;\n"
             "endprogram\n"
             "checker c;\n"
             "  bit x;\n"
             "  bit y;\n"
             "endchecker\n"
             "module top; i u(); p v(); c w(); endmodule\n"));
}

TEST(NameSpaceRedeclaration, TwoSpecparamsOfOneNameInASpecifyBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  specify\n"
             "    specparam d = 1;\n"
             "    specparam d = 2;\n"
             "  endspecify\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "redeclaration of specparam 'd' in the specify block", 4, "3.13"));
  ElabFixture g;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  specify\n"
             "    specparam d = 1, d = 2;\n"
             "  endspecify\n"
             "endmodule\n",
             g));
  EXPECT_TRUE(ReportedError(
      g.diag.Diagnostics(),
      "redeclaration of specparam 'd' in the specify block", 3, "3.13"));
}

TEST(NameSpaceRedeclaration, DistinctSpecparamsInASpecifyBlock) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  specify\n"
             "    specparam d = 1;\n"
             "    specparam e = 2, f = 3;\n"
             "  endspecify\n"
             "endmodule\n"));
}

TEST(NameSpaceRedeclaration, TwoSpecparamsOfOneNameInAModuleBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  specparam d = 1;\n"
             "  specparam d = 2;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'd'", 3, "23.9"));
  ElabFixture g;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  parameter int d = 1;\n"
             "  specparam d = 2;\n"
             "endmodule\n",
             g));
  EXPECT_TRUE(
      ReportedError(g.diag.Diagnostics(), "redeclaration of 'd'", 3, "23.9"));
}

TEST(NameSpaceRedeclaration, DistinctSpecparamsInAModuleBody) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int p = 1;\n"
             "  specparam d = 1;\n"
             "  specparam e = 2;\n"
             "endmodule\n"));
}

struct Redeclared {
  const char* src;
  const char* name;
  uint32_t line;
};

TEST(NameSpaceRedeclaration, UnitScopeNamesOfTwoKinds) {
  const Redeclared kCases[] = {
      {"function int f(); return 0; endfunction\nint f;\n", "f", 2},
      {"task t; endtask\nfunction void t(); endfunction\n", "t", 2},
      {"localparam int P = 1;\nint P;\n", "P", 2},
      {"event e;\nint e;\n", "e", 2},
      {"wire w;\nint w;\n", "w", 2},
      {"typedef int T;\nint T;\n", "T", 2},
      {"function int c(); return 0; endfunction\nchecker c; endchecker\n", "c",
       2},
  };
  for (const Redeclared& c : kCases) {
    ElabFixture f;
    EXPECT_FALSE(ElabOk(std::string(c.src) + "module top; endmodule\n", f))
        << c.src;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("redeclaration of '") + c.name +
                                  "' in compilation-unit scope",
                              c.line, "3.13"))
        << c.src;
  }
}

TEST(NameSpaceRedeclaration, UnitScopeNamesOfDistinctNames) {
  EXPECT_TRUE(
      ElabOk("function int f(); return 0; endfunction\n"
             "task t; endtask\n"
             "localparam int P = 1;\n"
             "event e;\n"
             "wire w;\n"
             "typedef int T;\n"
             "int g;\n"
             "module top; int f; int g; endmodule\n"));
}

TEST(NameSpaceRedeclaration, ModuleNameSpaceNamesOfTwoKinds) {
  const Redeclared kCases[] = {
      {"module top;\n"
       "  interface n; endinterface\n"
       "  logic n;\n"
       "endmodule\n",
       "n", 3},
      {"module top;\n"
       "  program n; endprogram\n"
       "  logic n;\n"
       "endmodule\n",
       "n", 3},
      {"program p;\n"
       "  logic foo;\n"
       "  task foo; endtask\n"
       "endprogram\n"
       "module top; p u(); endmodule\n",
       "foo", 3},
      {"checker c;\n"
       "  bit foo;\n"
       "  function bit foo(); return 0; endfunction\n"
       "endchecker\n"
       "module top; c u(); endmodule\n",
       "foo", 3},
  };
  for (const Redeclared& c : kCases) {
    ElabFixture f;
    EXPECT_FALSE(ElabOk(c.src, f)) << c.src;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("redeclaration of '") + c.name + "'",
                              c.line, "23.9"))
        << c.src;
  }
}

TEST(NameSpaceRedeclaration, ModuleNameSpaceNamesOfDistinctNames) {
  EXPECT_TRUE(
      ElabOk("program p;\n"
             "  logic foo;\n"
             "  task bar; endtask\n"
             "endprogram\n"
             "checker c;\n"
             "  bit foo;\n"
             "  function bit bar(); return 0; endfunction\n"
             "endchecker\n"
             "module top;\n"
             "  interface n; endinterface\n"
             "  program q; endprogram\n"
             "  logic m;\n"
             "  logic top;\n"
             "  p u();\n"
             "  c w();\n"
             "endmodule\n"));
}

TEST(NameSpaceRedeclaration, BlockNameSpaceNamesOfTwoKinds) {
  const Redeclared kCases[] = {
      {"module m;\n"
       "  initial begin\n"
       "    event e;\n"
       "    int e;\n"
       "  end\n"
       "endmodule\n",
       "e", 4},
      {"module m;\n"
       "  if (1) begin : g\n"
       "    int f;\n"
       "    function void f(); endfunction\n"
       "  end\n"
       "endmodule\n",
       "f", 4},
  };
  for (const Redeclared& c : kCases) {
    ElabFixture f;
    EXPECT_FALSE(ElabOk(c.src, f)) << c.src;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("redeclaration of '") + c.name + "'",
                              c.line, "23.9"))
        << c.src;
  }
}

TEST(NameSpaceRedeclaration, BlockNameSpaceNamesOfDistinctNames) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    event e;\n"
             "    int x;\n"
             "  end\n"
             "  if (1) begin : g\n"
             "    int v;\n"
             "    function void f(); endfunction\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceRedeclaration, APortsNameTakenByAnotherKind) {
  const Redeclared kCases[] = {
      {"module m(a);\n"
       "  input a;\n"
       "  parameter a = 1;\n"
       "endmodule\n",
       "a", 3},
      {"module m(a);\n"
       "  input a;\n"
       "  typedef int a;\n"
       "endmodule\n",
       "a", 3},
      {"interface i(a);\n"
       "  input a;\n"
       "  task a; endtask\n"
       "endinterface\n"
       "module top; wire w; i u(w); endmodule\n",
       "a", 3},
      {"program p(a);\n"
       "  input a;\n"
       "  function int a(); return 0; endfunction\n"
       "endprogram\n"
       "module top; wire w; p u(w); endmodule\n",
       "a", 3},
  };
  for (const Redeclared& c : kCases) {
    ElabFixture f;
    EXPECT_FALSE(ElabOk(c.src, f)) << c.src;
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("redeclaration of port '") + c.name + "'", c.line, "3.13"))
        << c.src;
  }
}

TEST(NameSpaceRedeclaration, APortsNameTakenByANetOrVariable) {
  EXPECT_TRUE(
      ElabOk("module m(a);\n"
             "  inout a;\n"
             "  wire a;\n"
             "endmodule\n"
             "interface i(a);\n"
             "  input a;\n"
             "  wire a;\n"
             "endinterface\n"
             "program p(a);\n"
             "  input a;\n"
             "  logic a;\n"
             "endprogram\n"
             "module top;\n"
             "  wire w;\n"
             "  m u(w);\n"
             "  i v(w);\n"
             "  p x(w);\n"
             "endmodule\n"));
}

TEST(NameSpaceRedeclaration, AnAttributesNameReadOutsideTheAttribute) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  (* a = 1 *) logic x;\n"
             "  initial x = a;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'a'", 3,
                            "23.9"));
}

TEST(NameSpaceRedeclaration, AVariableNamedLikeAnAttributeIsRead) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  (* a = 1 *) logic x;\n"
             "  logic a;\n"
             "  initial x = a;\n"
             "endmodule\n"));
}

}  // namespace
