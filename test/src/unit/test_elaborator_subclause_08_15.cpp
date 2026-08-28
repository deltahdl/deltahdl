#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SuperElaboration, SuperInDerivedMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer value;\n"
             "  function integer delay();\n"
             "    delay = value * value;\n"
             "  endfunction\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  integer value;\n"
             "  function integer delay();\n"
             "    delay = super.delay() + value * super.value;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  LinkedPacket lp;\n"
             "endmodule\n"));
}

// An initial block is not a class method at all, so what the elaborator
// enforces here is §8.11's rule that 'this' is confined to a non-static class
// method rather than §8.15's about a base class. The report stands at the
// `initial` keyword, since it is the procedure that is judged.
TEST(SuperElaboration, SuperInModuleBlockError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = super.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' shall only be used within non-static class methods", 2, "8.11"));
}

// Derived does extend Base, so §8.15 has nothing to say about this super; what
// it breaks is §8.10's rule that a static method references neither 'this' nor
// 'super'. That is the distinction SuperOutsideASubclassNames8_15 below turns
// on, and naming the subclause is what keeps the two apart.
TEST(SuperElaboration, SuperInStaticMethodError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  static function int get_x();\n"
      "    return super.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 5, "8.10"));
}

// §8.15: "The super keyword is used from within a derived class to refer to
// members, class value parameters, or local value parameters of the base
// class." A class that extends nothing has no base class for super to name.
// The subclause on the report is what tells this rejection from §8.10's rule
// about super in a static method, which the same keyword in a different
// position breaches.
TEST(SuperElaboration, SuperOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  function int get();\n"
      "    return super.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 3,
                            "8.15"));
}

TEST(SuperElaboration, SuperAccessInheritedMemberOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int get_x();\n"
             "    return super.x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperPropertyWriteInDerivedOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int x;\n"
             "  function void set();\n"
             "    super.x = 10;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.15 requires super.new to be the first statement executed in a
// constructor. A constructor whose super.new call is preceded by another
// statement violates the rule and must fail elaboration. The report the
// elaborator emits for it names §8.17, which is where the constructor's own
// subclause states the ordering, and it stands at the misplaced super.new()
// call rather than at the constructor.
TEST(SuperElaboration, SuperNewMustBeFirstStatementError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "  function new();\n"
      "    y = 1;\n"
      "    super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      9, "8.17"));
}

// The same constructor is legal when super.new leads the body, confirming the
// ordering check only rejects the misplaced case.
TEST(SuperElaboration, SuperNewFirstStatementOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int y;\n"
             "  function new();\n"
             "    super.new();\n"
             "    y = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.15 requires super.new to be the first statement *executed*. A super.new
// call nested inside a conditional can never satisfy that: the branch condition
// executes before it. This covers the control-flow input form of the rule,
// which travels a different validation path than a merely out-of-order
// sequential call, so it is rejected at elaboration. The report stands at the
// `if` rather than at the super.new() inside it, because it is the guarding
// statement that makes the call unreachable as the first one, and it names
// §8.17 as the misplaced sequential call above does.
TEST(SuperElaboration, SuperNewInsideConditionalError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "  function new();\n"
      "    if (y == 0) super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      8, "8.17"));
}

// §8.15 states that an expression reaching a base class value parameter
// through super is not a constant expression. A static variable initializer
// requires a constant expression, so initializing one from super.P (where P
// is the base's value parameter) must be rejected at elaboration. The super
// access is legal here because the enclosing method is a non-static method of
// a derived class. The report stands at the super keyword, which is where the
// member access the rule names begins.
TEST(SuperElaboration, SuperValueParamNotConstantError) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    static int s = super.P;\n"
      "    return s;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            5, "8.15"));
}

// §8.15 names both a value parameter and a local value parameter as the kinds
// of parameter whose super-qualified access is non-constant. The test above
// exercises the value-parameter form; this one covers the local value
// parameter (a localparam declared in the base class, per §6.20.4). Reaching it
// through super in a static-variable initializer, which requires a constant
// expression, must therefore also be rejected at elaboration. The super access
// itself is legal because f is a non-static method of a derived class. The
// message names the kind, which is what tells this rejection from the one
// above.
TEST(SuperElaboration, SuperLocalValueParamNotConstantError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  localparam int LP = 4;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    static int s = super.LP;\n"
      "    return s;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression using 'super' to access base class local value "
                    "parameter 'LP' is not a constant expression",
                    6, "8.15"));
}

// §8.15 states the rule for the expression, wherever it stands, so a report
// wired into the static-variable initializer alone leaves it unenforced
// everywhere else. §7.4.2 requires a fixed-size unpacked dimension to be a
// constant expression, which is a second such context and reaches the super
// access through a different field of the declaration than the initializer
// does.
TEST(SuperElaboration, SuperValueParamInUnpackedDimensionNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    int a[super.P];\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            5, "8.15"));
}

// §8.15's first sentence makes super the way to reach a base class value
// parameter, and only its last sentence bars the reach from a constant
// expression. Returning the parameter's value from a method requires no
// constant, so the same access that the tests above reject is accepted here.
TEST(SuperElaboration, SuperValueParamOutsideConstantContextOk) {
  EXPECT_TRUE(
      ElabOk("class Base #(parameter int P = 4);\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int get_p();\n"
             "    return super.P;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// Contrast control: the same static initializer context accepts a genuine
// constant, confirming the rejection above is caused by the super access
// being non-constant rather than by the static declaration itself.
TEST(SuperElaboration, StaticInitConstantOk) {
  EXPECT_TRUE(
      ElabOk("class Base #(parameter int P = 4);\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int f();\n"
             "    static int s = 4;\n"
             "    return s;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// The six cases below cover the child-statement links of Stmt that the §8.15
// walk in src/elaborator/elaborator_validate_class_members.cpp reaches for the
// first time now that CheckStmtConstantContexts takes its list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. That walk
// had written out seven of the thirteen links, so a declaration standing in one
// of the other six was never looked at and its initializer and its unpacked
// dimensions were exempt from the clause.
//
// Each source below declares `int a[super.P]` in one such position. §7.4.2
// requires a fixed-size unpacked dimension to be a constant expression, and
// §8.15's last sentence bars reaching a base class value parameter through
// 'super' where a constant expression is required, so the declaration is
// rejected wherever it stands. The report stands at the `super.P` expression,
// which CheckConstExprForSuperParam locates from Expr::range.
//
// Stmt::for_steps is the seventh link the walk gains and takes no case. A.6.8
// gives `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`, and none of the three declares a variable, so no
// conforming source puts a declaration there for this rule to read.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, so a fork holds
// declarations of its own, which Parser::ParseBlockVarDecls in
// src/parser/parser_stmt_block.cpp puts in Stmt::fork_stmts beside the
// statements. §13.4.4 admits the fork-join_none form inside a function.
TEST(SuperElaboration, SuperValueParamInAForkArmDeclarationNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    fork\n"
      "      int a[super.P];\n"
      "    join_none\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(SuperElaboration, SuperValueParamInAnAssertionPassStmtNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    assert (1) begin\n"
      "      int a[super.P];\n"
      "    end\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

TEST(SuperElaboration, SuperValueParamInAnAssertionFailStmtNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    assert (1) else begin\n"
      "      int a[super.P];\n"
      "    end\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.15 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(SuperElaboration, SuperValueParamInARandcaseItemNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    randcase\n"
      "      1 : begin\n"
      "        int a[super.P];\n"
      "      end\n"
      "    endcase\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            7, "8.15"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds a declaration directly.
// Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts it in
// RsProd::code_stmts, reached through Stmt::rs_productions and through no other
// member of Stmt.
TEST(SuperElaboration, SuperValueParamInARandsequenceCodeBlockNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    randsequence(main)\n"
      "      main : { int a[super.P]; };\n"
      "    endsequence\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, which the
// parser keeps in RsRule::weight_code rather than in RsProd::code_stmts. It is
// a second statement position under Stmt::rs_productions, so it gets its own
// case: the production `alt` below holds a null statement, which leaves the
// weight block as the only place the declaration stands.
TEST(SuperElaboration, SuperValueParamInARandsequenceWeightCodeBlockNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { int a[super.P]; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

}  // namespace
