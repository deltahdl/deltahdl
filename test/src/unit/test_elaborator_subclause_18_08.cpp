#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// 18.8: the rand_mode() method is built-in and cannot be overridden, so a class
// that declares a method of that name is illegal.
TEST(RandModeBuiltin, OverrideRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void rand_mode(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'rand_mode' is a built-in method and cannot be overridden", 3, "18.8"));
}

// 18.8: the override prohibition is by method name, independent of signature.
// Declaring rand_mode with the nonvoid (int, no-argument) query signature is
// just as illegal as the void form.
TEST(RandModeBuiltin, OverrideViaNonvoidSignatureRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int rand_mode();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'rand_mode' is a built-in method and cannot be overridden", 3, "18.8"));
}

// A class that defines an ordinary method and leaves rand_mode alone elaborates
// cleanly.
TEST(RandModeBuiltin, NonOverridingClassAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void toggle(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.8: a compiler error shall be issued if the variable named in a rand_mode()
// call does not exist within the object's class hierarchy.
TEST(RandModeNamedVariable, MissingVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.missing.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            8, "18.8"));
}

// 18.8: a compiler error shall be issued if the named variable exists but is
// not declared rand or randc. A plain (non-random) data member cannot be the
// subject of rand_mode().
TEST(RandModeNamedVariable, NonRandVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.y.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'y' is not declared rand or randc, so rand_mode() "
                            "cannot be applied to it",
                            9, "18.8"));
}

// §18.8: "A compiler error shall be issued if the specified variable does not
// exist within the class hierarchy or it exists but is not declared as rand or
// randc." The subclause on the report is what tells this rejection from
// §18.9's rule for constraint_mode(), whose message and location are the same
// shape one member access away.
TEST(RandModeNamedVariable, CalledOnANonRandomMemberNames18_8) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.y.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'y' is not declared rand or randc", 9, "18.8"));
}

// Naming a variable that is declared rand elaborates without error.
TEST(RandModeNamedVariable, RandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: a randc variable is a random variable too, so naming one in rand_mode()
// is legal.
TEST(RandModeNamedVariable, RandcVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  randc bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: the specified variable may be inherited from a base class -- it need
// only exist somewhere in the class hierarchy. Naming a base-class rand
// variable through a derived handle is legal.
TEST(RandModeNamedVariable, InheritedRandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: the no-name void form applies to every random variable in the object
// and names nothing to validate, so it elaborates cleanly.
TEST(RandModeNamedVariable, UnnamedFormAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: omitting the variable name is only allowed when rand_mode() is called
// as a void function -- i.e. with an on/off argument. A no-name call that also
// passes no argument is neither the void all-variables form nor the nonvoid
// query form (which must name a variable), so it is illegal.
TEST(RandModeNamedVariable, UnnamedQueryWithoutArgumentRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.rand_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            8, "18.8"));
}

// The fourteen cases below write a rand_mode() call into each statement link
// Elaborator::WalkStmtsForClassHandleOps in
// src/elaborator/elaborator_validate_class_handles.cpp did not read before
// #3319. That walk wrote out six of the thirteen links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h names, so a call one level down
// -- in a fork arm, a for header, an assertion action block, a randcase item or
// a randsequence code block -- reached neither §18.8 check.
//
// The two checks take a case each per link because they answer different
// sources and report different rules: CheckUnnamedRandModeHasArgument reads a
// call that names no variable and passes no argument, and
// CheckNamedRandModeVariableExists reads a call naming a variable the class
// hierarchy does not hold. The first seven cases are the former, the next seven
// the latter.
//
// Both reports stand at the call itself, so each case names the line its own
// call is written on. The handle is declared at module scope, which puts it in
// the map of handle types before any statement is walked.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, and A.6.9's
// subroutine_call_statement is one such statement.
TEST(RandModeNamedVariable, UnnamedRandModeQueryInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.rand_mode();\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`,
// whose right-hand side is an expression, and A.8.1 admits a subroutine call
// there. The nonvoid query form is what fits that position, and it is the
// form the rule is about.
TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.rand_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// takes the same expression on its right.
TEST(RandModeNamedVariable, UnnamedRandModeQueryInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.rand_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// one below it cover one arm each.
TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.rand_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            8, "18.8"));
}

TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.rand_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            8, "18.8"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The rule is about the source, so it holds whether the weighted draw
// would select the item or not.
TEST(RandModeNamedVariable, UnnamedRandModeQueryInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.rand_mode();\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, which Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt. RsRule::weight_code is the second statement position
// under that one link, and ForEachRandsequenceRuleStmt visits both.
TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.rand_mode(); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

// The same seven links for the named form, whose variable does not exist in
// the class hierarchy.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, and A.6.9's
// subroutine_call_statement is one such statement.
TEST(RandModeNamedVariable, MissingRandModeVariableInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.missing.rand_mode(0);\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`,
// whose right-hand side is an expression, and A.8.1 admits a subroutine call
// there. The nonvoid query form is what fits that position, and it is the
// form the rule is about.
TEST(RandModeNamedVariable,
     MissingRandModeVariableInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.missing.rand_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// takes the same expression on its right.
TEST(RandModeNamedVariable, MissingRandModeVariableInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.missing.rand_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// one below it cover one arm each.
TEST(RandModeNamedVariable,
     MissingRandModeVariableInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.missing.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            8, "18.8"));
}

TEST(RandModeNamedVariable,
     MissingRandModeVariableInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.missing.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            8, "18.8"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The rule is about the source, so it holds whether the weighted draw
// would select the item or not.
TEST(RandModeNamedVariable, MissingRandModeVariableInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.missing.rand_mode(0);\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, which Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt. RsRule::weight_code is the second statement position
// under that one link, and ForEachRandsequenceRuleStmt visits both.
TEST(RandModeNamedVariable,
     MissingRandModeVariableInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.missing.rand_mode(0); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

}  // namespace
