#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The report stands at the method's own declaration rather than at the
// statement holding 'this', because §8.10's rule is about the method: the
// elaborator scans a static method's body and reports the method once.
TEST(StaticMethodElaboration, StaticMethodThisError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function int get_x();\n"
      "    return this.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, StaticMethodSuperError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function void foo(); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  static function void bar();\n"
      "    super.foo();\n"
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

TEST(StaticMethodElaboration, StaticMethodAccessingStaticPropertyOk) {
  EXPECT_TRUE(
      ElabOk("class id;\n"
             "  static int current;\n"
             "  static function int next_id();\n"
             "    return current;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  id i;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, NonStaticMethodThisOk) {
  EXPECT_TRUE(
      ElabOk("class Demo;\n"
             "  int x;\n"
             "  function void set_x(int val);\n"
             "    this.x = val;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Demo d;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, StaticMethodNoThisSuperOk) {
  EXPECT_TRUE(
      ElabOk("class Util;\n"
             "  static function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Util u;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, StaticMethodCallsStaticMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Util;\n"
             "  static int count;\n"
             "  static function void inc();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "  static function void inc_twice();\n"
             "    inc();\n"
             "    inc();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Util u;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, StaticMethodThisInConditionError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function int check();\n"
      "    if (this.x > 0) return 1;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, StaticMethodThisInAssignmentError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function void reset();\n"
      "    this.x = 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, StaticTaskThisError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task set_x();\n"
      "    this.x = 5;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, UnqualifiedNonStaticPropertyError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function void f();\n"
      "    x = 5;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, UnqualifiedNonStaticMethodCallError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  function void helper(); endfunction\n"
      "  static function void f();\n"
      "    helper();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, LocalShadowsNonStaticOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function void f();\n"
             "    int x;\n"
             "    x = 5;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, ParamShadowsNonStaticOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function void f(int x);\n"
             "    x = 5;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// The line names which of the two static methods broke the rule: id is clean
// and bad is not, so the report stands at bad's declaration and a test naming
// line 3 would be answering for a method the source never faulted.
TEST(StaticMethodElaboration, StaticMethodThisInCallArgError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function int id(int v);\n"
      "    return v;\n"
      "  endfunction\n"
      "  static function int bad();\n"
      "    return id(this.x);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 6, "8.10"));
}

// The fourteen cases below cover the child-statement links of Stmt that the two
// §8.10 walks in src/elaborator/elaborator_validate_class_members.cpp reach for
// the first time now that both take their list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. StmtRefsNonStaticMember, which
// finds the access, had written out six of the thirteen links, and
// CollectLocalNames, which records the names a body declares and so which
// references resolve locally, seven. A reference in a link the first was
// missing was never looked at, and a declaration in a link the second was
// missing left the name out of the set.
//
// The two are converted together because either alone is wrong: the reporter
// alone would report an access to a name the block does declare, and the
// collector alone would suppress a report nothing was making. So each link
// takes a pair of cases writing the same statement in the same position, one
// naming the class property, which §8.10 rejects, and one naming a variable the
// block declares itself, which shadows the property and is accepted. Only the
// pair tells the two walks apart.
//
// The report stands at the method's own declaration, on line 3 of every source
// below, because §8.10's rule is about the method:
// Elaborator::ValidateOneClassStaticMethods scans a static method's body and
// reports the method once.

// §8.10: "A static method has no access to non-static members (class properties
// or methods)", and it puts no condition on the statement the access is written
// in. A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, so a fork holds
// both halves of this pair: the statement here, and the declaration in the case
// below it, which Parser::ParseBlockVarDecls in
// src/parser/parser_stmt_block.cpp puts in Stmt::fork_stmts beside the
// statements.
TEST(StaticMethodElaboration, NonStaticPropertyWrittenInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    fork\n"
      "      x = 5;\n"
      "    join\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, LocalDeclaredInAForkArmShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    fork\n"
             "      int x;\n"
             "      x = 5;\n"
             "    join\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, so a
// for header assigns to a variable that may be any variable in scope, the class
// property among them. The loop's control variable is declared above the loop
// here, which leaves the header's assignment as the only access in the source.
TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInAForInitializationIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    int i;\n"
      "    for (x = 0; i < 2; i = i + 1) ;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, so a for step writes a
// variable the same way, and the class property is one such variable. None of
// the three declares a name, so this link takes the access case alone: no
// conforming source puts a declaration in a for step for CollectLocalNames to
// find.
TEST(StaticMethodElaboration, NonStaticPropertyWrittenInAForStepIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    int i;\n"
      "    for (i = 0; i < 2; x = x + 1) ;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. The four cases
// through the next pair cover one arm each.
TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    assert (1) x = 5;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInAnAssertionPassStmtShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    assert (1) begin\n"
             "      int x;\n"
             "      x = 5;\n"
             "    end\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    assert (1) else x = 5;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInAnAssertionFailStmtShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    assert (1) else begin\n"
             "      int x;\n"
             "      x = 5;\n"
             "    end\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.10 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    randcase\n"
      "      1 : x = 5;\n"
      "    endcase\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, LocalDeclaredInARandcaseItemShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    randcase\n"
             "      1 : begin\n"
             "        int x;\n"
             "        x = 5;\n"
             "      end\n"
             "    endcase\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds both halves of this pair
// directly. Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// them in RsProd::code_stmts, reached through Stmt::rs_productions and through
// no other member of Stmt.
TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    randsequence(main)\n"
      "      main : { x = 5; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInARandsequenceCodeBlockShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    randsequence(main)\n"
             "      main : { int x; x = 5; };\n"
             "    endsequence\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, which the
// parser keeps in RsRule::weight_code rather than in RsProd::code_stmts. It is
// a second statement position under Stmt::rs_productions, so it takes its own
// pair: the production `alt` below holds a null statement, which leaves the
// weight block as the only place the access and the declaration stand.
TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { x = 5; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInARandsequenceWeightCodeBlockShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    randsequence(main)\n"
             "      main : alt := 5 { int x; x = 5; };\n"
             "      alt : { ; };\n"
             "    endsequence\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

}  // namespace
