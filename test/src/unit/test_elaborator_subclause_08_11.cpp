#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The report stands at the `initial` keyword rather than at the statement that
// names 'this': Elaborator::ValidateThisInItem passes the module item's own
// location.
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

// §8.11 holds for every procedural block a module can contain, not just
// `always`. Elaborator::ValidateThisInItem selects the item kinds it checks
// with IsProceduralItemKind in src/parser/ast_module.h, which names
// always_comb alongside always, always_ff, always_latch, initial and final.
// The report stands at the `always_comb` keyword, the module item's own
// location.
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

// §8.11 lists type(this) as a permitted form alongside non-static class
// methods, constraints, inlined constraint methods, and covergroups embedded
// in classes. Static method bodies otherwise forbid bare 'this', yet the
// literal type(this) form may still appear there because §6.23 names it as
// a way to obtain the enclosing class type without evaluating any expression.
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

// §8.11 — a static method is not tied to any instance, so a non-literal 'this'
// (here `this.x`) inside a static method body is outside the permitted set and
// an error is issued. This is the static-method rejection form, a different
// enforcement path from the module-context rejections above:
// CheckStaticMethodsForThisSuper in
// src/elaborator/elaborator_validate_static_methods.cpp reports it under §8.10,
// which is where the standard states that a static method has no 'this', and
// the report stands at the `function` keyword.
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

// §8.11 also permits 'this' inside a covergroup embedded within a class.
// The validator must not flag a reference to 'this' when the enclosing
// context is a class-member covergroup.
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

// §8.11 also permits 'this' inside a class constraint block. The
// validator must not flag such a reference when the enclosing context is
// the body of a constraint declared on a class.
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

// The exception is restricted to the literal form type(this). A 'this' that
// appears as part of a richer expression inside type(...) is still subject
// to §8.11, and inside a static method body the rejection is the §8.10 one
// CheckStaticMethodsForThisSuper emits, at the `function` keyword.
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

// §8.11 gives `this` no object outside a class's non-static methods, and a
// subroutine a package or the compilation unit declares is no method of any
// class, so `this` in one is reported as in a module's subroutine.
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

// §8.11 gives `this` no object outside a class, and a continuous assignment
// and a declaration's initializer belong to no method, so `this` or `super` in
// either side of the one or in the other is reported at the module item, as in
// a procedural block (#8079).
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

// §8.11 reaches every expression a statement holds, not only an assignment's
// two sides and a condition: a block variable's initializer, a loop's
// condition and a delay each name `this` here, in a procedural block apiece,
// and each block is reported at its keyword (#8080).
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

// §8.11 reaches `this` wherever it stands within an expression, a
// part-select's second bound and a replication's count among the rest (#8086).
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
