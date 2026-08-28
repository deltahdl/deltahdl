#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// 18.9: constraint_mode() is a built-in method and cannot be overridden, so a
// class that declares a method of that name is illegal.
TEST(ConstraintModeBuiltin, OverrideRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function void constraint_mode(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'constraint_mode' is a built-in method and cannot be overridden", 4,
      "18.9"));
}

// 18.9: the override prohibition is by method name, independent of signature.
// Declaring constraint_mode with the nonvoid (int, no-argument) query
// signature is just as illegal as the void form.
TEST(ConstraintModeBuiltin, OverrideViaNonvoidSignatureRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function int constraint_mode();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'constraint_mode' is a built-in method and cannot be overridden", 4,
      "18.9"));
}

// A class that defines an ordinary method and leaves constraint_mode alone
// elaborates cleanly.
TEST(ConstraintModeBuiltin, NonOverridingClassAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function void toggle(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.9: the constraint named in a constraint_mode() call shall exist in the
// object's class hierarchy. Naming a constraint block that does not exist is a
// compile-time error.
TEST(ConstraintModeNamedBlock, MissingConstraintRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.missing.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    9, "18.9"));
}

// Naming a constraint block that does exist on the object's class elaborates
// without error.
TEST(ConstraintModeNamedBlock, ExistingConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.filter1.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// A constraint block inherited from a base class counts as existing in the
// hierarchy, so naming it is legal.
TEST(ConstraintModeNamedBlock, InheritedConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint base_c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "  constraint deriv_c { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.base_c.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.9: the existence check searches the whole class hierarchy, so a name that
// appears in neither the derived class nor any of its base classes is the
// error case. This exercises the multi-level walk returning "not found" across
// two levels, distinct from the single-class rejection.
TEST(ConstraintModeNamedBlock, MissingConstraintAcrossHierarchyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint base_c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "  constraint deriv_c { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.nonexistent.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'nonexistent' does not exist in the "
                            "hierarchy of class 'Derived'",
                            13, "18.9"));
}

// 18.9: the no-name form applies to every constraint in the object and is
// allowed only as a void call. Because it names no constraint block, the
// existence check shall not fire: a call with no constraint identifier
// elaborates cleanly even though no block named "constraint_mode" exists.
TEST(ConstraintModeNamedBlock, UnnamedFormNotTreatedAsMissingBlock) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.9: omitting the constraint name is allowed only in the void form, which
// takes an on/off argument. A call that names no constraint and passes no
// argument is neither a legal void call nor a legal nonvoid query (the query
// form must name a block), so it is rejected.
TEST(ConstraintModeNamedBlock, UnnamedNoArgQueryRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    q = p.constraint_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

// 18.9: the nonvoid query form is legal when it names a constraint block. This
// guards the no-name/no-argument rejection above from over-firing: a named,
// argument-less constraint_mode() query still elaborates cleanly.
TEST(ConstraintModeNamedBlock, NamedNoArgQueryAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    q = p.filter1.constraint_mode();\n"
             "  end\n"
             "endmodule\n"));
}

// The fourteen cases below write a constraint_mode() call into each statement
// link Elaborator::WalkStmtsForClassHandleOps in
// src/elaborator/elaborator_validate_class_handles.cpp did not read before
// #3319. That walk wrote out six of the thirteen links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h names, so a call one level down
// -- in a fork arm, a for header, an assertion action block, a randcase item or
// a randsequence code block -- reached neither §18.9 check.
//
// The two checks take a case each per link because they answer different
// sources and report different rules: CheckUnnamedConstraintModeHasArgument
// reads a call that names no constraint block and passes no argument, and
// CheckNamedConstraintModeExists reads a call naming a block the class
// hierarchy does not hold. The first seven cases are the former, the next seven
// the latter.
//
// Both reports stand at the call itself, so each case names the line its own
// call is written on. The handle is declared at module scope, which puts it in
// the map of handle types before any statement is walked.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, and A.6.9's
// subroutine_call_statement is one such statement.
TEST(ConstraintModeNamedBlock, UnnamedConstraintModeQueryInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.constraint_mode();\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`,
// whose right-hand side is an expression, and A.8.1 admits a subroutine call
// there. The nonvoid query form is what fits that position, and it is the
// form the rule is about.
TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.constraint_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// takes the same expression on its right.
TEST(ConstraintModeNamedBlock, UnnamedConstraintModeQueryInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.constraint_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// one below it cover one arm each.
TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.constraint_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            9, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.constraint_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            9, "18.9"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The rule is about the source, so it holds whether the weighted draw
// would select the item or not.
TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.constraint_mode();\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, which Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt. RsRule::weight_code is the second statement position
// under that one link, and ForEachRandsequenceRuleStmt visits both.
TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.constraint_mode(); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

// The same seven links for the named form, whose constraint block does not
// exist in the class hierarchy.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, and A.6.9's
// subroutine_call_statement is one such statement.
TEST(ConstraintModeNamedBlock, MissingConstraintModeBlockInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.missing.constraint_mode(0);\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`,
// whose right-hand side is an expression, and A.8.1 admits a subroutine call
// there. The nonvoid query form is what fits that position, and it is the
// form the rule is about.
TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.missing.constraint_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// takes the same expression on its right.
TEST(ConstraintModeNamedBlock, MissingConstraintModeBlockInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.missing.constraint_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// one below it cover one arm each.
TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.missing.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    9, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.missing.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    9, "18.9"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The rule is about the source, so it holds whether the weighted draw
// would select the item or not.
TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.missing.constraint_mode(0);\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, which Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt. RsRule::weight_code is the second statement position
// under that one link, and ForEachRandsequenceRuleStmt visits both.
TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.missing.constraint_mode(0); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

}  // namespace
