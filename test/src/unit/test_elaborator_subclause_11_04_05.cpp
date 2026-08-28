#include <string>

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, LogicalEqualityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalInequalityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryCaseEqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 === 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryCaseNeqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !== 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EqualityOperatorElaboration, AlwaysCombEqualityCheck) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic y;\n"
      "  always_comb y = (a == b);\n"
      "  initial begin\n"
      "    a = 8'h42;\n"
      "    b = 8'h42;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(EqualityOperatorElaboration, BlockingAssignComparisonOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int r_eq, r_ne, r_lt, r_gt, r_le, r_ge;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    r_eq = (a == b);\n"
      "    r_ne = (a != b);\n"
      "    r_lt = (a < b);\n"
      "    r_gt = (a > b);\n"
      "    r_le = (a <= b);\n"
      "    r_ge = (a >= b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_eq = f.ctx.FindVariable("r_eq");
  auto* r_ne = f.ctx.FindVariable("r_ne");
  auto* r_lt = f.ctx.FindVariable("r_lt");
  auto* r_gt = f.ctx.FindVariable("r_gt");
  auto* r_le = f.ctx.FindVariable("r_le");
  auto* r_ge = f.ctx.FindVariable("r_ge");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_ne, nullptr);
  ASSERT_NE(r_lt, nullptr);
  ASSERT_NE(r_gt, nullptr);
  ASSERT_NE(r_le, nullptr);
  ASSERT_NE(r_ge, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 0u);
  EXPECT_EQ(r_ne->value.ToUint64(), 1u);
  EXPECT_EQ(r_lt->value.ToUint64(), 1u);
  EXPECT_EQ(r_gt->value.ToUint64(), 0u);
  EXPECT_EQ(r_le->value.ToUint64(), 1u);
  EXPECT_EQ(r_ge->value.ToUint64(), 0u);
}

TEST(OperatorElaboration, ChandleEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ChandleInequalityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h != null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5: comparing a class handle with the literal null using the logical
// equality operator is a legal operation, so elaboration reports no error.
TEST(OperatorElaboration, ClassHandleEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  logic r;\n"
      "  initial r = (c == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5: the rule permits a class-handle comparison when one operand is
// assignment compatible with the other. A base handle and a handle of a class
// derived from it satisfy that requirement, and case equality (===) is one of
// the permitted operators, so this comparison elaborates cleanly.
TEST(OperatorElaboration, ClassHandleCaseEqualityCompatibleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module m;\n"
      "  Base b;\n"
      "  Derived d;\n"
      "  logic r;\n"
      "  initial r = (b === d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5 states "The logical equality (or case equality) operator is a legal
// operation if either operand is a class handle or the literal null, and one of
// the operands is assignment compatible with the other." Two handles of
// unrelated classes are not assignment compatible, so the equality comparison
// is rejected. This is the discriminating negative for the compatibility
// requirement above.
TEST(OperatorElaboration, ClassHandleEqualityIncompatibleRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  logic r;\n"
      "  initial r = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle comparison requires assignment compatible", 7, "11.4.5"));
}

// §11.4.5: case equality (===) is one of the operators the rule permits between
// a chandle and the literal null, so this comparison elaborates without error.
// Complements the ==/!= chandle-null cases with the case-equality operator
// form.
TEST(OperatorElaboration, ChandleCaseEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h === null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5: two handles of the same class type are trivially assignment
// compatible, so a logical-equality (==) comparison between them is a legal
// operation and elaborates cleanly. Covers the == operator on two class handles
// (the base/derived case above uses ===).
TEST(OperatorElaboration, ClassHandleEqualitySameTypeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  C b;\n"
      "  logic r;\n"
      "  initial r = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.22.2 makes two variables of different named structure types
// non-equivalent, so CheckAggregateCompareOp in
// src/elaborator/elaborator_validate_operations.cpp rejects a comparison of one
// against the other and names both type names in the report.
// WalkStmtsForAggregateCompare carries that rule down a statement tree. It
// wrote out six of the thirteen child-statement links Stmt declares and now
// takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h, so the seven cases below cover
// one newly reached position each. Each source elaborated clean before the
// conversion: the walk never descended into the position, so the comparison
// reached CheckAggregateCompareOp through nothing.
//
// §11.4.5 is the equality operators these comparisons are written with, and
// §6.22.2 is the rule the report names, because it is what decides that two
// aggregate operands of different named types may not be compared.
//
// `stmt` is written at line 8 of the source and may run to several lines, so
// the line the report stands at is read back out of the source rather than
// counted.
void ExpectNonEquivalentAggregateCompareIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  typedef struct { logic [7:0] a; } s_t;\n"
      "  typedef struct { logic [15:0] b; } t_t;\n"
      "  s_t s;\n"
      "  t_t t;\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "comparison of non-equivalent aggregate types 's_t' and 't_t'",
      LineHolding(src, "s == t"), "6.22.2"));
}

// §9.3.2 gives `fork { statement_or_null } join`, whose arms the parser keeps
// in Stmt::fork_stmts.
TEST(OperatorElaboration, NonEquivalentAggregateCompareInAForkArm) {
  ExpectNonEquivalentAggregateCompareIn(
      "fork\n"
      "      r = (s == t);\n"
      "    join");
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, so an equality
// expression stands in a for-loop initialization. The parser keeps those
// assignments in Stmt::for_inits.
TEST(OperatorElaboration, NonEquivalentAggregateCompareInAForInit) {
  ExpectNonEquivalentAggregateCompareIn(
      "for (r = (s == t); r == 0; r = 0) r = 1;");
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// is a variable_lvalue, an assignment_operator and an expression, so the
// equality expression stands in a for-loop step as well. The parser keeps those
// in Stmt::for_steps.
TEST(OperatorElaboration, NonEquivalentAggregateCompareInAForStep) {
  ExpectNonEquivalentAggregateCompareIn(
      "for (r = 0; r == 0; r = (s == t)) r = 1;");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(OperatorElaboration, NonEquivalentAggregateCompareInAnAssertionPassStmt) {
  ExpectNonEquivalentAggregateCompareIn("assert (r) r = (s == t);");
}

TEST(OperatorElaboration, NonEquivalentAggregateCompareInAnAssertionFailStmt) {
  ExpectNonEquivalentAggregateCompareIn("assert (r) else r = (s == t);");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §6.22.2 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(OperatorElaboration, NonEquivalentAggregateCompareInARandcaseItem) {
  ExpectNonEquivalentAggregateCompareIn("randcase 1: r = (s == t); endcase");
}

// §18.17 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(OperatorElaboration,
     NonEquivalentAggregateCompareInARandsequenceCodeBlock) {
  ExpectNonEquivalentAggregateCompareIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = (s == t); };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
