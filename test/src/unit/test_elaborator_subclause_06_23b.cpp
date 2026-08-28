#include <string>

#include "fixture_elaborator.h"
#include "helpers_generate_elab.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Counts variables in `mod` whose name ends in `last`. A declaration inside an
// (unnamed) generate block reaches the module's variable list under a scoped
// name, so the trailing character identifies which alternative was taken.
int CountVarsEndingWith(const RtlirModule* mod, char last) {
  int count = 0;
  for (const auto& var : mod->variables) {
    if (!var.name.empty() && var.name.back() == last) ++count;
  }
  return count;
}

TEST(TypeOperatorElab, TypeOfThisInClassMethodAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static function type(this) get();\n"
             "    return null;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, TypeRefComparedToIntegerLiteralRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (type(T) == 5) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

TEST(TypeOperatorElab, TypeRefComparedToTypeRefAccepted) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  initial begin\n"
             "    if (type(T) == type(int)) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, NonTypeRefSideOfCaseEqRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (type(T) === 0) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

TEST(TypeOperatorElab, TypeRefComparedToVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  int v;\n"
      "  initial begin\n"
      "    if (type(T) != v) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 4,
      "6.23"));
}

// The §6.23 rule is symmetric: a non-type-reference operand is rejected
// whether it appears on the left or the right of the comparison.
TEST(TypeOperatorElab, NonTypeRefLeftOfCompareRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (7 == type(T)) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

// §6.23 — the prohibition extends to the bang-equal form.
TEST(TypeOperatorElab, NonTypeRefBangEqRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (type(T) !== 0) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

// §6.23 — the inner expression of type(...) shall not contain a
// hierarchical reference. A member-access subtree is treated as a
// hierarchical reference here.
TEST(TypeOperatorElab, HierarchicalRefInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m;\n"
      "  sub s();\n"
      "  var type(s.q) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not contain a hierarchical reference", 6,
      "6.23"));
}

// §6.23 — even when wrapped in a larger expression, a member-access
// subtree inside type(...) is rejected.
TEST(TypeOperatorElab, HierarchicalRefInBinaryArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m;\n"
      "  sub s();\n"
      "  var type(s.q + 1) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not contain a hierarchical reference", 6,
      "6.23"));
}

// §6.23 — the inner expression of type(...) shall not reference an
// element of a dynamic object. A select whose base names a dynamic array
// is the smallest such reference.
TEST(TypeOperatorElab, DynamicArrayElementInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[];\n"
      "  var type(d[0]) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      3, "6.23"));
}

// §6.23 — an associative array is also a dynamic object; selecting an
// element of one inside type(...) is rejected.
TEST(TypeOperatorElab, AssocArrayElementInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[string];\n"
      "  var type(a[\"k\"]) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      3, "6.23"));
}

// §6.23 — a queue is a variable-size (dynamic) object as well, so selecting one
// of its elements inside type(...) is rejected, just like a dynamic or
// associative array element. This exercises the queue input form of the
// dynamic-object prohibition.
TEST(TypeOperatorElab, QueueElementInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  var type(q[0]) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      3, "6.23"));
}

// §6.23 — a comparison of two type references is a constant expression, and the
// two references compare equal exactly when the referenced types match
// (§6.22.1) This is the accepting path for the `==` form: with `T` bound to
// `int`, the generate-if condition is true, so the then-block's declaration
// reaches the module and the else-block's does not. Observing which declaration
// survives shows the elaborator actually folding the comparison to true via
// type matching, not merely accepting the syntax.
TEST(TypeOperatorGenerate, EqualMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) == type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

// §6.23 — the rejecting path for `==`: `int` and `real` are nonmatching types,
// so the condition folds to false and the else-block is the one instantiated.
TEST(TypeOperatorGenerate, EqualNonMatchingTypesSelectsElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) == type(real)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

// §6.23 — the inequality form negates the match result: nonmatching types make
// `!=` true, selecting the then-block.
TEST(TypeOperatorGenerate, NotEqualNonMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) != type(real)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

// §6.23 — the case-equality operator behaves the same as equality for type
// references: matching types fold `===` to true, selecting the then-block.
TEST(TypeOperatorGenerate, CaseEqualMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) === type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

// §6.23 — the case-inequality operator negates the match, so matching types
// fold `!==` to false and the else-block is instantiated.
TEST(TypeOperatorGenerate, CaseNotEqualMatchingTypesSelectsElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) !== type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

// §6.23 — both operands may be built-in data-type references rather than type
// parameters. `int` (signed) and `bit` (unsigned) are nonmatching, so the
// condition folds to false; the else-block is taken. This exercises the
// data-type (text) operand form of the fold, distinct from the type-parameter
// (identifier) form above.
TEST(TypeOperatorGenerate, BuiltinDataTypeReferencesFoldByMatching) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (type(int) == type(bit)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

// §6.23 — the comparison being a constant expression must hold for each kind of
// constant type operand, which take different resolution paths. The parameter
// form is covered above; here the operand is a `localparam type`, and the
// generate-if still folds by type matching (localparam T bound to `int` matches
// `type(int)`), selecting the then-block.
TEST(TypeOperatorGenerate, LocalparamTypeOperandFoldsByMatching) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  localparam type T = int;\n"
      "  if (type(T) == type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

// A class declaring two typedefs of the same width and opposite signedness, so
// that a lookup reaching the wrong member is visible in the signedness rather
// than passing on a coincidence of width. `payload_t` is 8-bit signed and
// `beat_t` is 8-bit unsigned. The class stands ahead of the module because
// `Parser::ParseTypeRefExpr` resolves `Frame::payload_t` as a data type only
// once `Frame` is in the parser's known types.
constexpr const char* kFrameClass =
    "class Frame;\n"
    "  typedef byte payload_t;\n"
    "  typedef logic [7:0] beat_t;\n"
    "endclass\n";

// §8.23 — the type operator is one of the contexts in which a class scope
// resolution may prefix a type name, so `type(Frame::payload_t)` names the
// typedef declared in `Frame`. The width and signedness are the assertion: the
// declaration elaborates to a 1-bit unsigned logic when the prefix is not
// resolved, which the absence of a diagnostic alone would not show.
TEST(TypeOperatorElab, ClassScopedTypedefVarDeclAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kFrameClass) +
                                  "module m;\n"
                                  "  var type(Frame::payload_t) v;\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
  EXPECT_TRUE(v->is_signed);
}

// §8.23 — the same for a net declaration, which reaches the check by a separate
// path through `Elaborator::ElaborateNetDecl`. The typedef is `beat_t` and not
// `payload_t` because §6.7.1 requires a net's data type to be 4-state, and
// `byte` is 2-state.
TEST(TypeOperatorElab, ClassScopedTypedefNetDeclAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kFrameClass) +
                                  "module m;\n"
                                  "  wire type(Frame::beat_t) w;\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirNet* w = FindNet(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->width, 8u);
  EXPECT_FALSE(w->is_signed);
}

// §6.23 — exempting `::` does not exempt `.`: a member access into a module
// instance is still a hierarchical reference and is still rejected. The
// diagnostic and its subclause are what is asserted, so the test cannot pass on
// a rejection some other rule produced.
TEST(TypeOperatorElab, InstanceMemberInTypeArgStillRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m;\n"
      "  sub s();\n"
      "  var type(s.q) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not contain a hierarchical reference", 6,
      "6.23"));
}

// §6.23 — the exemption §8.23 grants applies to the scope resolution node
// itself and not to the subtree under it. `C::x.y` is a `.` member access whose
// left side is a `::` scope resolution, so the outer node is a hierarchical
// reference and the declaration is rejected.
TEST(TypeOperatorElab, MemberAccessOverScopeResolutionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  var type(C::x.y) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not contain a hierarchical reference", 5,
      "6.23"));
}

// §8.23 — the type-parameter-default form of the operator carries the class
// scope prefix as well, so `P` binds to `Frame::payload_t` and a variable
// declared with `P` is 8-bit signed. Losing the prefix binds `P` to a
// `payload_t` that no scope declares, which nothing diagnoses.
TEST(TypeOperatorElab, ClassScopedTypedefAsTypeParamDefault) {
  ElabFixture f;
  auto* design =
      ElaborateSrc(std::string(kFrameClass) +
                       "module m;\n"
                       "  localparam type P = type(Frame::payload_t);\n"
                       "  P v;\n"
                       "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
  EXPECT_TRUE(v->is_signed);
}

// §6.23 rules that "A type reference used in an equality, inequality, case
// equality, or case inequality comparison shall only be compared with another
// type reference", and A.10 admits a type_reference primary under those four
// operators alone. CheckTypeRefCompareOp in
// src/elaborator/elaborator_validate_operations.cpp is that rule, and
// WalkStmtsForTypeRefCompare carries it down a statement tree.
//
// That walk wrote out six of the thirteen child-statement links Stmt declares
// and now takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The seven cases below cover
// one newly reached position each, and every one of them elaborated clean
// before the conversion because the walk never descended into the position.
//
// `stmt` is written at line 4 of the source and may run to several lines, so
// the line the report stands at is read back out of the source rather than
// counted.
void ExpectTypeRefComparedToLiteralIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m #(parameter type T = int) ();\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference",
      LineHolding(src, "type(T) == 5"), "6.23"));
}

// §9.3.2 gives `fork { statement_or_null } join`, whose arms the parser keeps
// in Stmt::fork_stmts.
TEST(TypeOperatorElab, TypeRefComparedToLiteralInAForkArm) {
  ExpectTypeRefComparedToLiteralIn(
      "fork\n"
      "      r = (type(T) == 5);\n"
      "    join");
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, so the comparison
// stands in a for-loop initialization, which the parser keeps in
// Stmt::for_inits.
TEST(TypeOperatorElab, TypeRefComparedToLiteralInAForInit) {
  ExpectTypeRefComparedToLiteralIn(
      "for (r = (type(T) == 5); r == 0; r = 0) r = 1;");
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// ends in an expression, so the comparison stands in a for-loop step, which the
// parser keeps in Stmt::for_steps.
TEST(TypeOperatorElab, TypeRefComparedToLiteralInAForStep) {
  ExpectTypeRefComparedToLiteralIn(
      "for (r = 0; r == 0; r = (type(T) == 5)) r = 1;");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(TypeOperatorElab, TypeRefComparedToLiteralInAnAssertionPassStmt) {
  ExpectTypeRefComparedToLiteralIn("assert (r) r = (type(T) == 5);");
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInAnAssertionFailStmt) {
  ExpectTypeRefComparedToLiteralIn("assert (r) else r = (type(T) == 5);");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §6.23 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(TypeOperatorElab, TypeRefComparedToLiteralInARandcaseItem) {
  ExpectTypeRefComparedToLiteralIn("randcase 1: r = (type(T) == 5); endcase");
}

// §18.17 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(TypeOperatorElab, TypeRefComparedToLiteralInARandsequenceCodeBlock) {
  ExpectTypeRefComparedToLiteralIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = (type(T) == 5); };\n"
      "      endsequence\n"
      "    end");
}

// §6.23 rules that the expression the type operator is applied to "shall not
// contain any hierarchical references or references to elements of dynamic
// objects", and a select of a dynamic array element is the smallest such
// reference. CheckTypeRefArgInner in
// src/elaborator/elaborator_validate_operations.cpp is that rule, and
// WalkStmtsForTypeRefArg carries it down a statement tree.
//
// That walk wrote out six of the thirteen child-statement links Stmt declares
// and now takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The seven cases below cover
// one newly reached position each. The type reference is written as one operand
// of a comparison against `type(int)`, which is the position A.10 gives a
// type_reference in an expression, so that the offending operand reaches the
// walk through Stmt::lhs and Stmt::rhs rather than through a declaration:
// A.6.8 admits no data_declaration in a for-loop step, so a declaration cannot
// cover all seven positions and a comparison can.
//
// `stmt` is written at line 5 of the source and may run to several lines, so
// the line the report stands at is read back out of the source rather than
// counted.
void ExpectDynamicElementInTypeArgIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  int d[];\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      LineHolding(src, "type(d[0])"), "6.23"));
}

// §9.3.2 gives `fork { statement_or_null } join`, whose arms the parser keeps
// in Stmt::fork_stmts.
TEST(TypeOperatorElab, DynamicElementInTypeArgInAForkArm) {
  ExpectDynamicElementInTypeArgIn(
      "fork\n"
      "      r = (type(d[0]) == type(int));\n"
      "    join");
}

// A.6.8's for_initialization reaches an expression through
// `variable_assignment ::= variable_lvalue = expression`, which the parser
// keeps in Stmt::for_inits.
TEST(TypeOperatorElab, DynamicElementInTypeArgInAForInit) {
  ExpectDynamicElementInTypeArgIn(
      "for (r = (type(d[0]) == type(int)); r == 0; r = 0) r = 1;");
}

// A.6.8's for_step_assignment reaches an expression through
// operator_assignment, which the parser keeps in Stmt::for_steps.
TEST(TypeOperatorElab, DynamicElementInTypeArgInAForStep) {
  ExpectDynamicElementInTypeArgIn(
      "for (r = 0; r == 0; r = (type(d[0]) == type(int))) r = 1;");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(TypeOperatorElab, DynamicElementInTypeArgInAnAssertionPassStmt) {
  ExpectDynamicElementInTypeArgIn("assert (r) r = (type(d[0]) == type(int));");
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInAnAssertionFailStmt) {
  ExpectDynamicElementInTypeArgIn(
      "assert (r) else r = (type(d[0]) == type(int));");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry.
TEST(TypeOperatorElab, DynamicElementInTypeArgInARandcaseItem) {
  ExpectDynamicElementInTypeArgIn(
      "randcase 1: r = (type(d[0]) == type(int)); endcase");
}

// §18.17 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions alone.
TEST(TypeOperatorElab, DynamicElementInTypeArgInARandsequenceCodeBlock) {
  ExpectDynamicElementInTypeArgIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = (type(d[0]) == type(int)); };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
