#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ThisElaboration, ThisInModuleInitialBlockError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = this.data;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 2,
      "8.11"));
}

TEST(ThisElaboration, ThisInModuleAlwaysBlockError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic clk;\n"
      "  always @(posedge clk) begin\n"
      "    automatic int x;\n"
      "    x = this.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 3,
      "8.11"));
}

TEST(ThisElaboration, ThisInModuleAlwaysCombBlockError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int y;\n"
      "  always_comb y = this.data;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 3,
      "8.11"));
}

TEST(ThisElaboration, ThisInModuleFunctionError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function int get_val();\n"
      "    return this.val;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 2,
      "8.11"));
}

TEST(ThisElaboration, ThisInNonStaticClassMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Demo;\n"
             "  integer x;\n"
             "  function new(integer x);\n"
             "    this.x = x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Demo d;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInRegularMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int data;\n"
             "  function int get_data();\n"
             "    return this.data;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, NoThisReferencesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = 42;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInModuleTaskError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  task do_work();\n"
      "    automatic int x;\n"
      "    x = this.data;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 2,
      "8.11"));
}

TEST(ThisElaboration, ThisInClassTaskOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int data;\n"
             "  task set_data(int d);\n"
             "    this.data = d;\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, BareThisInModuleInitialError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = this;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 2,
      "8.11"));
}

TEST(ThisElaboration, BareThisInClassMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  function C get_self();\n"
             "    return this;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, TypeOfThisInStaticMethodBodyAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static function int f();\n"
             "    int b;\n"
             "    if (type(this) == type(int)) b = 1;\n"
             "    return b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInStaticMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function int f();\n"
      "    return this.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'this' and 'super' shall not be used in a static "
                            "method",
                            3, "8.10"));
}

TEST(ThisElaboration, ThisInClassCovergroupOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg;\n"
             "    coverpoint this.x;\n"
             "  endgroup\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInClassConstraintBlockOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { this.x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInsideMemberAccessInsideTypeOpRejected) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  static function int f();\n"
      "    int b;\n"
      "    if (type(this.x) == type(int)) b = 1;\n"
      "    return b;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'this' and 'super' shall not be used in a static "
                            "method",
                            2, "8.10"));
}

TEST(ThisElaboration, ThisInAPackageOrUnitSubroutineIsAnError) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  int x;\n"
      "  function void f(); this.x = 1; endfunction\n"
      "endpackage\n"
      "int y;\n"
      "task t(); this.y = 1; endtask\n"
      "module m; endmodule\n",
      f);
  for (const int kLine : {3, 6}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "'this' has no object to refer to outside a non-static class method",
        kLine, "8.11"))
        << kLine;
  }
}

TEST(ThisElaboration, ThisInAModuleItemsOwnExpressionIsAnError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int y;\n"
      "  logic q;\n"
      "  wire [31:0] w = this.y;\n"
      "  int z = this.y;\n"
      "  assign y = super.y;\n"
      "  assign this.q = 1'b1;\n"
      "endmodule\n",
      f);
  for (const int kLine : {4, 5, 6, 7}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "'this' has no object to refer to outside a non-static class method",
        kLine, "8.11"))
        << kLine;
  }
}

TEST(ThisElaboration, ThisInAnyExpressionOfAStatementIsAnError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int y;\n"
      "  initial begin\n"
      "    automatic int x = this.y;\n"
      "  end\n"
      "  initial for (int i = 0; i < this.y; i++) ;\n"
      "  initial #(this.y) ;\n"
      "endmodule\n",
      f);
  for (const int kLine : {3, 6, 7}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "'this' has no object to refer to outside a non-static class method",
        kLine, "8.11"))
        << kLine;
  }
}

TEST(ThisElaboration, ThisInAnyOperandOfAnExpressionIsAnError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  logic [3:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial x = v[3:this.y];\n"
      "  initial r = {this.y{1'b1}};\n"
      "endmodule\n",
      f);
  for (const int kLine : {5, 6}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "'this' has no object to refer to outside a non-static class method",
        kLine, "8.11"))
        << kLine;
  }
}

constexpr const char* kNoObject =
    "'this' has no object to refer to outside a non-static class method";

TEST(ThisElaboration, ThisInAnInterfaceOrProgramIsAnError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  typedef type(this) self_t;\n"
      "  function C self(); return this; endfunction\n"
      "endclass\n"
      "interface ifc; int v; initial v = this.v; endinterface\n"
      "program pg; int v; initial v = this.v; endprogram\n"
      "module t;\n"
      "  ifc i();\n"
      "  pg p();\n"
      "endmodule\n",
      f);
  for (const int kLine : {5, 6}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoObject, kLine, "8.11"))
        << kLine;
  }
  for (const int kLine : {2, 3}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

TEST(ThisElaboration,
     DISABLED_ThisInAGenerateBlockOrAPropertyInitializerIsAnError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x = 3;\n"
      "  int y = this.x;\n"
      "  static int s = this.x;\n"
      "  function int m(); return this.x; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int g;\n"
      "  if (1) begin : gb\n"
      "    initial g = this.g;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const int kLine : {3, 4, 10}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoObject, kLine, "8.11"))
        << kLine;
  }
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 5));
}

TEST(ThisElaboration, DISABLED_AssignmentToAParameterThroughThisIsReported) {
  ElabFixture f;
  ElabOk(
      "class C #(int P = 3);\n"
      "  localparam int L = 2;\n"
      "  int x;\n"
      "  function void w(); this.P = 4; endfunction\n"
      "  function void w2(); this.L = 4; endfunction\n"
      "  function void w3(); this.x = 4; endfunction\n"
      "  function void w4(); P = 4; endfunction\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'L'",
                            5, "6.20"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 6));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            7, "6.20"));
}

TEST(ThisElaboration, ParameterThroughThisInAStaticMethodIsReported) {
  ElabFixture f;
  ElabOk(
      "class C #(int P = 3);\n"
      "  static function int s(); return this.P; endfunction\n"
      "  function int m(); return this.P; endfunction\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'this' and 'super' shall not be used in a static "
                            "method",
                            2, "8.10"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 3));
}

TEST(ThisElaboration, DISABLED_ThisNamingNoMemberIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class A;\n"
      "  int x;\n"
      "  function new(); this.cnew = 1; endfunction\n"
      "  function void f(); this.nosuch = 0; endfunction\n"
      "  function void g(); x = this.nope; endfunction\n"
      "  function void h(); this.nf(); endfunction\n"
      "  task t(); this.tq = 1; endtask\n"
      "  function void ok(); this.x = 1; x = this.x; endfunction\n"
      "endclass\n"
      "package p;\n"
      "  class PA;\n"
      "    int x;\n"
      "    function void f(); this.y = 1; endfunction\n"
      "    function void ok(); this.x = 1; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class MA;\n"
      "    int x;\n"
      "    function void f(); this.y = 1; endfunction\n"
      "    function void ok(); this.x = 1; endfunction\n"
      "    class NA;\n"
      "      function void f(); this.x = 1; endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "  A a;\n"
      "  initial a = new;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (auto [line, member] :
       std::initializer_list<std::pair<int, const char*>>{{3, "cnew"},
                                                          {4, "nosuch"},
                                                          {5, "nope"},
                                                          {6, "nf"},
                                                          {7, "tq"},
                                                          {13, "y"},
                                                          {20, "y"},
                                                          {23, "x"}}) {
    EXPECT_TRUE(ReportedError(
        diags, std::string("has no member named '") + member + "'", line,
        "8.11"))
        << line;
  }
  for (const int kLine : {8, 14, 21}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
