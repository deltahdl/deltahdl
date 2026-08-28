#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassObjectElaboration, NullLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassObjectElaboration, ClassHandleAssignNull) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = null;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleAssignHandle) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleEqualityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a == b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleCaseEqualityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a === b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleInequalityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a != null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleConditionalAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b, c;\n"
             "  initial begin\n"
             "    automatic int sel;\n"
             "    a = sel ? b : c;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleArithmeticError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

// §8.4 lists every operator valid on an object handle -- equality, case
// equality, the conditional operator, and assignment of a compatible handle or
// of null -- and Table 8-1 records arithmetic on a handle as not allowed. The
// subclause on the report is what tells this rejection from an ordinary type
// mismatch in the same assignment, which is §10.8's rule and not §8.4's.
TEST(ClassObjectElaboration, ArithmeticOnAnObjectHandleNames8_4) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleRelationalError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a < b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleBitwiseError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a & b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleLogicalNegationError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = !a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleIncrementError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleShiftError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a << 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleCompoundAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a += 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on class object handle is illegal", 6,
                            "8.4"));
}

// The subclause asserted is the one the emission site passes, and
// Elaborator::ValidateClassHandleContAssign in
// src/elaborator/elaborator_validate_class_handles.cpp passes §10.3, where a
// continuous assignment's driver is defined, rather than §8.4.
TEST(ClassObjectElaboration, ClassHandleContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class object handle cannot be used in continuous assignment", 4,
      "10.3"));
}

TEST(ClassObjectElaboration, ClassVariableElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Pkt;\n"
      "  int data;\n"
      "endclass\n"
      "module top;\n"
      "  Pkt p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassObjectElaboration, ClassHandleAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p1, p2;\n"
             "    p1 = new;\n"
             "    p2 = p1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleCaseInequalityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a !== b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleEqualityWithNullAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a == null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleDecrementError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a--;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleCompareCompatibleOk) {
  EXPECT_TRUE(
      ElabOk("class Base; endclass\n"
             "class Child extends Base; endclass\n"
             "module m;\n"
             "  Base b;\n"
             "  Child c;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (b == c);\n"
             "  end\n"
             "endmodule\n"));
}

// §8.4 allows == and != on two handles; which pairs of handles they may be
// applied to is §11.4.5's "one of the operands is assignment compatible with
// the other". That is the subclause the site in
// src/elaborator/elaborator_validate_class_handles.cpp passes for two
// unrelated classes, so it is the one asserted here.
TEST(ClassObjectElaboration, ClassHandleCompareIncompatibleError) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle comparison requires assignment compatible types", 8,
      "11.4.5"));
}

TEST(ClassObjectElaboration, ClassHandleAssignCompatibleOk) {
  EXPECT_TRUE(
      ElabOk("class Base; endclass\n"
             "class Child extends Base; endclass\n"
             "module m;\n"
             "  Base b;\n"
             "  Child c;\n"
             "  initial b = c;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleAssignIncompatibleError) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle assignment requires assignment compatible types", 6,
      "8.4"));
}

// Table 8-1 lists casting of a SystemVerilog object handle as "Limited" (in
// contrast to the unrestricted casting of a C pointer). One consequence of that
// limit is that a handle cannot be reinterpreted as an unrelated non-class
// value: casting it to a plain integral type is rejected.
TEST(ClassObjectElaboration, ClassHandleCastToNonClassTypeError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = int'(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot cast class object handle to a non-class "
                            "type",
                            6, "8.4"));
}

// The dual of the previous check: the limited casting of Table 8-1 also forbids
// producing a class handle out of an ordinary (non-class, non-null) value, so
// casting an integer literal to a class type is rejected.
TEST(ClassObjectElaboration, NonClassValueCastToClassTypeError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a = C'(5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot cast non-class value to a class type", 4,
                            "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleAssignParentToChildError) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class Child extends Base; endclass\n"
      "module m;\n"
      "  Base b;\n"
      "  Child c;\n"
      "  initial c = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle assignment requires assignment compatible types", 6,
      "8.4"));
}

// The eight cases below write one §8.4 breach -- `r = a + 1;`, which Table 8-1
// records as not allowed on an object handle -- into each statement link
// Elaborator::WalkStmtsForClassHandleOps in
// src/elaborator/elaborator_validate_class_handles.cpp did not read before
// #3319. That walk wrote out six of the thirteen links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h names, so the same arithmetic
// one level down, in a fork arm or a randcase item, elaborated clean.
//
// The report stands at the offending expression rather than at the enclosing
// method, because CheckClassHandleBinary anchors it at Expr::range.start, so
// each case names the line its own arithmetic is written on.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser puts in Stmt::fork_stmts.
TEST(ClassObjectElaboration, ArithmeticOnAHandleInAForkArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    fork\n"
      "      r = a + 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`,
// whose right-hand side is an ordinary expression and so may name a handle.
TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInAForInitializationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    for (r = a + 1; r < 2; r = r + 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// takes the same expression on its right.
TEST(ClassObjectElaboration, ArithmeticOnAHandleInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    for (r = 0; r < 2; r = a + 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// one below it cover one arm each.
TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    assert (1) r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    assert (1) else r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.4 is a rule about the source, so it holds whether the weighted draw
// would select the item or not.
TEST(ClassObjectElaboration, ArithmeticOnAHandleInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    randcase\n"
      "      1 : r = a + 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, which Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt.
TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    randsequence(main)\n"
      "      main : { r = a + 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, which the
// parser keeps in RsRule::weight_code rather than in RsProd::code_stmts. It is
// a second statement position under Stmt::rs_productions, so it takes its own
// case: the production `alt` holds a null statement, which leaves the weight
// block as the only place the arithmetic stands.
TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { r = a + 1; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

}  // namespace
