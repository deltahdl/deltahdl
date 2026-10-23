#include <gtest/gtest.h>

#include <initializer_list>

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
// applied to is §11.4.5's requirement that one operand be assignment compatible
// with the other. That is the subclause the site in
// src/elaborator/elaborator_validate_class_handles.cpp passes for two unrelated
// classes, so it is the one asserted here.
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

// §7.8 and §7.4.6: `C m[string]` declares an associative array whose elements
// are handles, and `m["a"]` selects an element, so the member `m["a"].v` is
// no §8.4 bit-select of a handle. ValidateVarDeclTypes took every variable of
// a class type for one handle, and the element select was reported.
TEST(ClassObjectElaboration, ElementSelectOfAnArrayOfHandlesIsNoBitSelect) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int v; endclass\n"
      "module m;\n"
      "  C h[string];\n"
      "  C a[2];\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = h[\"a\"].v + a[1].v;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "bit-select on class object handle is illegal", 7,
                             "8.4"));
}

// §7.4.2 (printed pages 153-154): a fixed-size unpacked array is declared by
// the dimension after the name, so a block's `C arr[2]` and a dynamic `C d[]`
// (§7.5) are arrays whose elements are handles, and `arr[1]` and `d[0]` are
// elements, not §8.4's (printed 181) bit-select of a handle. The module-scope
// declaration read its unpacked dimensions (ValidateVarDeclTypes), but
// WalkStmtsForClassHandleOps took every block item declaration of a class
// type for one handle, so the write `arr[1] = new` and the read `arr[1].v`
// were both reported.
TEST(ClassObjectElaboration,
     ElementSelectOfABlockDeclaredArrayOfHandlesIsNoBitSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; int v = 7; endclass\n"
      "module m;\n"
      "  int r;\n"
      "  initial begin\n"
      "    C arr[2];\n"
      "    C d[];\n"
      "    arr[1] = new;\n"
      "    d = new[2];\n"
      "    d[0] = new;\n"
      "    r = arr[1].v * 10 + d[0].v;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A block-declared handle with no unpacked dimension is one handle, and a
// select of it stays §8.4's bit-select; the array exemption reads the
// dimensions, not the block position.
TEST(ClassObjectElaboration, BitSelectOfABlockDeclaredHandleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    C h;\n"
      "    r = h[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on class object handle is illegal", 6,
                            "8.4"));
}

// §8.4's rules on what a handle admits hold wherever the expression stands: in
// a module's task or function, through a formal argument, and in a class
// method, through a property of the class, as in a procedural block. An array
// of handles is no handle, so a select of it is an element, and a function
// returning a handle names a handle variable, so assigning one to it is legal.
TEST(ClassObjectElaboration,
     HandleOperationsAreCheckedInSubroutinesAndMethods) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class D;\n"
      "  C c;\n"
      "  C cs[2];\n"
      "  function void f(); int x; x = c + 1; x = cs.size(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h;\n"
      "  int r;\n"
      "  task t(); r = h + 1; endtask\n"
      "  function int g(C a); return a + 1; endfunction\n"
      "  function C k(); k = h; endfunction\n"
      "  initial r = h + 1;\n"
      "endmodule\n",
      f);
  for (const int kLine : {5, 10, 11, 13}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "operator is not allowed on class object handles",
                              kLine, "8.4"))
        << kLine;
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "class object handle", 12, "8.4"));
}

// §8.4's rules are about the handle value, whatever expression yields it: a
// property of a class type selected from a handle, an element of an array of
// handles and a function's result are each handles, while a property, element
// or result of any other type, a structure's member and a package's variable
// are not.
TEST(ClassObjectElaboration, AHandleYieldedByAnExpressionIsAHandle) {
  ElabFixture f;
  ElabOk(
      "class N; N next; int x; int arr[2]; endclass\n"
      "package q; int v; endpackage\n"
      "module m;\n"
      "  N h, hs[2];\n"
      "  int ia[2];\n"
      "  typedef struct { int f; } s_t;\n"
      "  s_t s;\n"
      "  function N make(); return null; endfunction\n"
      "  function int ifn(); return 0; endfunction\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = h.next + 1;\n"
      "    r = hs[0] + 1;\n"
      "    r = make() + 1;\n"
      "    r = h.x + 1;\n"
      "    r = ia[0] + 1;\n"
      "    r = ifn() + 1;\n"
      "    r = s.f + 1;\n"
      "    r = q::v + 1;\n"
      "    r = h.arr + 1;\n"
      "    r = h.nosuch + 1;\n"
      "    r = h[0] + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "operator is not allowed on class object handles";
  for (const int kLine : {12, 13, 14}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "8.4"))
        << kLine;
  }
  for (const int kLine : {15, 16, 17, 18, 19, 20, 21}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "8.4"))
        << kLine;
  }
}

// §11.3.6 with §8.4: an assignment written in parentheses stands within an
// expression, and one of a compatible handle, another of the target's class,
// of a class extending it, or null, writes a handle of the target's class,
// which a method is called through or compared like any other.
TEST(ClassObjectElaboration, AParenthesizedHandleAssignmentIsAHandle) {
  EXPECT_TRUE(
      ElabOk("class C; task run(); endtask endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  C h; C g = new; D d = new; logic b;\n"
             "  initial begin\n"
             "    ((h = g)).run();\n"
             "    b = ((h = d)) == null;\n"
             "    b = ((h = null)) == null;\n"
             "  end\n"
             "endmodule\n"));
}

// §11.3.6 with §8.4 and §7.4: a parenthesized assignment of a handle to an
// element of an array of handles, or to a structure member holding one, is
// written as the assignment statement is.
TEST(ClassObjectElaboration, AParenthesizedAssignmentToAHandleElement) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  typedef struct { C h; } s_t;\n"
             "  C arr [2]; C g = new; s_t s; logic b;\n"
             "  initial begin\n"
             "    b = ((arr[0] = g)) == null;\n"
             "    b = ((s.h = g)) == null;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.4: a parenthesized assignment of a handle of an unrelated class is no
// assignment of a compatible handle.
TEST(ClassObjectElaboration, AParenthesizedIncompatibleHandleAssignment) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class E; endclass\n"
      "module m;\n"
      "  C h; E e = new; logic b;\n"
      "  initial b = ((h = e)) == null;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle assignment requires assignment compatible types", 5,
      "8.4"));
}

// §8.4: a parenthesized assignment writes no integral value into a handle.
TEST(ClassObjectElaboration, AParenthesizedIntegralAssignmentToAHandle) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C h; logic b;\n"
      "  initial b = ((h = 1)) == null;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign non-class value to class object handle", 4, "8.4"));
}

// §8.4: a parenthesized assignment writes no handle into an integral variable.
TEST(ClassObjectElaboration, AParenthesizedHandleAssignmentToAnInt) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C g = new; int n; logic b;\n"
      "  initial b = ((n = g)) == 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 4, "8.4"));
}

// §8.4: a compound assignment written in parentheses is an arithmetic
// operator on the handle, which no handle admits.
TEST(ClassObjectElaboration, AParenthesizedCompoundAssignmentToAHandle) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C h; logic b;\n"
      "  initial b = ((h += 1)) == null;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

}  // namespace
