#include <gtest/gtest.h>

#include <initializer_list>

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

}  // namespace
