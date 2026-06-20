#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_map>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

using Values = std::unordered_map<std::string, int64_t>;

// A guard leaf that always reports a fixed four-state value, used to model the
// atomic subexpressions of a guard predicate in isolation.
GuardPredicate ConstantLeaf(GuardValue v) {
  GuardPredicate leaf;
  leaf.op = GuardPredicate::Op::kLeaf;
  leaf.leaf_fn = [v](const Values&) { return v; };
  return leaf;
}

// 18.5.12 / Figure 18-3: the conjunction of two guard subexpressions. A FALSE
// operand forces FALSE even when the other operand would error or is random;
// otherwise an ERROR operand forces ERROR; otherwise RANDOM propagates; only
// two TRUE operands give TRUE.
TEST(ConstraintGuard4State, ConjunctionTruthTable) {
  EXPECT_EQ(GuardAnd(GuardValue::kFalse, GuardValue::kFalse),
            GuardValue::kFalse);
  EXPECT_EQ(GuardAnd(GuardValue::kFalse, GuardValue::kTrue),
            GuardValue::kFalse);
  EXPECT_EQ(GuardAnd(GuardValue::kFalse, GuardValue::kError),
            GuardValue::kFalse);
  EXPECT_EQ(GuardAnd(GuardValue::kFalse, GuardValue::kRandom),
            GuardValue::kFalse);

  EXPECT_EQ(GuardAnd(GuardValue::kTrue, GuardValue::kFalse),
            GuardValue::kFalse);
  EXPECT_EQ(GuardAnd(GuardValue::kTrue, GuardValue::kTrue), GuardValue::kTrue);
  EXPECT_EQ(GuardAnd(GuardValue::kTrue, GuardValue::kError),
            GuardValue::kError);
  EXPECT_EQ(GuardAnd(GuardValue::kTrue, GuardValue::kRandom),
            GuardValue::kRandom);

  EXPECT_EQ(GuardAnd(GuardValue::kError, GuardValue::kFalse),
            GuardValue::kFalse);
  EXPECT_EQ(GuardAnd(GuardValue::kError, GuardValue::kTrue),
            GuardValue::kError);
  EXPECT_EQ(GuardAnd(GuardValue::kError, GuardValue::kError),
            GuardValue::kError);
  EXPECT_EQ(GuardAnd(GuardValue::kError, GuardValue::kRandom),
            GuardValue::kError);

  EXPECT_EQ(GuardAnd(GuardValue::kRandom, GuardValue::kFalse),
            GuardValue::kFalse);
  EXPECT_EQ(GuardAnd(GuardValue::kRandom, GuardValue::kTrue),
            GuardValue::kRandom);
  EXPECT_EQ(GuardAnd(GuardValue::kRandom, GuardValue::kError),
            GuardValue::kError);
  EXPECT_EQ(GuardAnd(GuardValue::kRandom, GuardValue::kRandom),
            GuardValue::kRandom);
}

// 18.5.12 / Figure 18-3: the disjunction of two guard subexpressions. A TRUE
// operand forces TRUE even when the other would error or is random; otherwise
// an ERROR operand forces ERROR; otherwise RANDOM propagates; only two FALSE
// operands give FALSE.
TEST(ConstraintGuard4State, DisjunctionTruthTable) {
  EXPECT_EQ(GuardOr(GuardValue::kFalse, GuardValue::kFalse),
            GuardValue::kFalse);
  EXPECT_EQ(GuardOr(GuardValue::kFalse, GuardValue::kTrue), GuardValue::kTrue);
  EXPECT_EQ(GuardOr(GuardValue::kFalse, GuardValue::kError),
            GuardValue::kError);
  EXPECT_EQ(GuardOr(GuardValue::kFalse, GuardValue::kRandom),
            GuardValue::kRandom);

  EXPECT_EQ(GuardOr(GuardValue::kTrue, GuardValue::kFalse), GuardValue::kTrue);
  EXPECT_EQ(GuardOr(GuardValue::kTrue, GuardValue::kTrue), GuardValue::kTrue);
  EXPECT_EQ(GuardOr(GuardValue::kTrue, GuardValue::kError), GuardValue::kTrue);
  EXPECT_EQ(GuardOr(GuardValue::kTrue, GuardValue::kRandom), GuardValue::kTrue);

  EXPECT_EQ(GuardOr(GuardValue::kError, GuardValue::kFalse),
            GuardValue::kError);
  EXPECT_EQ(GuardOr(GuardValue::kError, GuardValue::kTrue), GuardValue::kTrue);
  EXPECT_EQ(GuardOr(GuardValue::kError, GuardValue::kError),
            GuardValue::kError);
  EXPECT_EQ(GuardOr(GuardValue::kError, GuardValue::kRandom),
            GuardValue::kError);

  EXPECT_EQ(GuardOr(GuardValue::kRandom, GuardValue::kFalse),
            GuardValue::kRandom);
  EXPECT_EQ(GuardOr(GuardValue::kRandom, GuardValue::kTrue), GuardValue::kTrue);
  EXPECT_EQ(GuardOr(GuardValue::kRandom, GuardValue::kError),
            GuardValue::kError);
  EXPECT_EQ(GuardOr(GuardValue::kRandom, GuardValue::kRandom),
            GuardValue::kRandom);
}

// 18.5.12 / Figure 18-3: negation passes ERROR and RANDOM through unchanged and
// swaps TRUE with FALSE.
TEST(ConstraintGuard4State, NegationTruthTable) {
  EXPECT_EQ(GuardNot(GuardValue::kFalse), GuardValue::kTrue);
  EXPECT_EQ(GuardNot(GuardValue::kTrue), GuardValue::kFalse);
  EXPECT_EQ(GuardNot(GuardValue::kError), GuardValue::kError);
  EXPECT_EQ(GuardNot(GuardValue::kRandom), GuardValue::kRandom);
}

// 18.5.12: the final value of the evaluated predicate selects the outcome. A
// TRUE result generates an unconditional constraint, FALSE eliminates it with
// no error, ERROR generates an error so randomize() fails, and RANDOM
// generates a conditional constraint.
TEST(ConstraintGuard4State, FinalOutcomeMapping) {
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kTrue), GuardOutcome::kUnconditional);
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kFalse), GuardOutcome::kEliminated);
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kError), GuardOutcome::kError);
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kRandom), GuardOutcome::kConditional);
}

// 18.5.12: the operators are applied recursively until every subexpression is
// evaluated. Here ((TRUE && error) || !FALSE) sifts the error: the conjunction
// is ERROR, but disjunction with !FALSE == TRUE forces the whole guard TRUE.
TEST(ConstraintGuardTree, RecursiveEvaluationSiftsError) {
  GuardPredicate conj;
  conj.op = GuardPredicate::Op::kAnd;
  conj.operands.push_back(ConstantLeaf(GuardValue::kTrue));
  conj.operands.push_back(ConstantLeaf(GuardValue::kError));

  GuardPredicate neg;
  neg.op = GuardPredicate::Op::kNot;
  neg.operands.push_back(ConstantLeaf(GuardValue::kFalse));

  GuardPredicate root;
  root.op = GuardPredicate::Op::kOr;
  root.operands.push_back(conj);
  root.operands.push_back(neg);

  EXPECT_EQ(EvaluateGuard(root, Values{}), GuardValue::kTrue);
}

// 18.5.12: a malformed subexpression (a leaf with no evaluator) is treated as
// an evaluation error, which then propagates through the operators.
TEST(ConstraintGuardTree, MissingLeafIsError) {
  GuardPredicate leaf;  // op defaults to kLeaf with no leaf_fn.
  EXPECT_EQ(EvaluateGuard(leaf, Values{}), GuardValue::kError);
}

// 18.5.12: recursive evaluation preserves a RANDOM result when no operator
// resolves it away. Here (TRUE && (FALSE || RANDOM)) folds the inner
// disjunction to RANDOM and the conjunction leaves it RANDOM, so the whole
// predicate is RANDOM and would generate a conditional constraint.
TEST(ConstraintGuardTree, RecursiveEvaluationYieldsRandom) {
  GuardPredicate disj;
  disj.op = GuardPredicate::Op::kOr;
  disj.operands.push_back(ConstantLeaf(GuardValue::kFalse));
  disj.operands.push_back(ConstantLeaf(GuardValue::kRandom));

  GuardPredicate root;
  root.op = GuardPredicate::Op::kAnd;
  root.operands.push_back(ConstantLeaf(GuardValue::kTrue));
  root.operands.push_back(disj);

  EXPECT_EQ(EvaluateGuard(root, Values{}), GuardValue::kRandom);
  EXPECT_EQ(GuardFinalOutcome(EvaluateGuard(root, Values{})),
            GuardOutcome::kConditional);
}

// 18.5.12: a constraint guard gates the creation of a constraint and is not a
// relation the solver must satisfy. With the guard FALSE the guarded range is
// eliminated, so an otherwise-unsatisfiable constraint imposes nothing and the
// variable ranges freely.
TEST(ConstraintGuardSolver, FalseGuardEliminatesConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  // An impossible range: it would never be satisfiable if it were imposed.
  guarded.lo = 200;
  guarded.hi = 300;
  guarded.has_guard = true;
  guarded.guard = ConstantLeaf(GuardValue::kFalse);
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 100);
}

// 18.5.12: a TRUE guard generates the guarded constraint unconditionally, so
// the guarded range is enforced on the solved value.
TEST(ConstraintGuardSolver, TrueGuardImposesConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  guarded.lo = 10;
  guarded.hi = 20;
  guarded.has_guard = true;
  guarded.guard = ConstantLeaf(GuardValue::kTrue);
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 10);
  EXPECT_LE(solver.GetValue("x"), 20);
}

// 18.5.12: when a guard evaluates to ERROR an unconditional error is generated
// and the constraint fails, so randomize() fails.
TEST(ConstraintGuardSolver, ErrorGuardFailsRandomize) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  guarded.lo = 10;
  guarded.hi = 20;
  guarded.has_guard = true;
  guarded.guard = ConstantLeaf(GuardValue::kError);
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

// 18.5.12: an ERROR that is not sifted away still fails randomize(). Here the
// guard is the conjunction (TRUE && error): no FALSE operand masks the error,
// so the conjunction is ERROR and the solve fails even though the guarded range
// would itself be satisfiable.
TEST(ConstraintGuardSolver, UnsiftedErrorFromConjunctionFailsRandomize) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  GuardPredicate guard;
  guard.op = GuardPredicate::Op::kAnd;
  guard.operands.push_back(ConstantLeaf(GuardValue::kTrue));
  guard.operands.push_back(ConstantLeaf(GuardValue::kError));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  guarded.lo = 10;  // satisfiable on its own; only the guard's error fails it
  guarded.hi = 20;
  guarded.has_guard = true;
  guarded.guard = guard;
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

// 18.5.12: negation passes an ERROR through unchanged, so a guard of the form
// !(error) is still ERROR and randomize() fails.
TEST(ConstraintGuardSolver, NegatedErrorFailsRandomize) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  GuardPredicate guard;
  guard.op = GuardPredicate::Op::kNot;
  guard.operands.push_back(ConstantLeaf(GuardValue::kError));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  guarded.lo = 10;
  guarded.hi = 20;
  guarded.has_guard = true;
  guarded.guard = guard;
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

// 18.5.12: treating guard subexpressions in the four-state logic prevents the
// solver from generating evaluation errors on seemingly correct constraints.
// Here a subexpression that errors (a null handle comparison) is conjoined with
// a FALSE subexpression; the conjunction is FALSE, so the error is sifted away
// and the guarded — otherwise unsatisfiable — constraint is simply eliminated.
TEST(ConstraintGuardSolver, ErrorSiftedByFalseConjunctSucceeds) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  GuardPredicate guard;
  guard.op = GuardPredicate::Op::kAnd;
  guard.operands.push_back(ConstantLeaf(GuardValue::kError));
  guard.operands.push_back(ConstantLeaf(GuardValue::kFalse));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  guarded.lo = 200;
  guarded.hi = 300;
  guarded.has_guard = true;
  guarded.guard = guard;
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 100);
}

// 18.5.12: an erroring subexpression disjoined with a TRUE subexpression sifts
// the error to a TRUE guard, so the guarded constraint is generated and
// enforced without any error being raised.
TEST(ConstraintGuardSolver, ErrorSiftedByTrueDisjunctImposesConstraint) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  GuardPredicate guard;
  guard.op = GuardPredicate::Op::kOr;
  guard.operands.push_back(ConstantLeaf(GuardValue::kError));
  guard.operands.push_back(ConstantLeaf(GuardValue::kTrue));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  guarded.lo = 30;
  guarded.hi = 40;
  guarded.has_guard = true;
  guarded.guard = guard;
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 30);
  EXPECT_LE(solver.GetValue("x"), 40);
}

// 18.5.12: a guard is characterized by involving only constants, state
// variables, and object handle comparisons; it is evaluated against the
// current state before the constraints are solved. Here the guard leaf reads a
// non-random state variable "mode": only when it holds is the guarded range
// imposed, so the same constraint block gates differently per state.
TEST(ConstraintGuardSolver, GuardReadsStateVariable) {
  GuardPredicate guard;
  guard.op = GuardPredicate::Op::kLeaf;
  guard.leaf_fn = [](const Values& vals) {
    auto it = vals.find("mode");
    if (it == vals.end()) return GuardValue::kError;
    return it->second == 1 ? GuardValue::kTrue : GuardValue::kFalse;
  };

  ConstraintExpr guarded;
  guarded.kind = ConstraintKind::kRange;
  guarded.var_name = "x";
  guarded.lo = 50;
  guarded.hi = 60;
  guarded.has_guard = true;
  guarded.guard = guard;

  // mode == 1: the guard is TRUE, the guarded range applies.
  {
    ConstraintSolver solver(99);
    RandVariable mode;
    mode.name = "mode";
    mode.min_val = 1;
    mode.max_val = 1;
    solver.AddVariable(mode);
    RandVariable x;
    x.name = "x";
    x.min_val = 0;
    x.max_val = 100;
    solver.AddVariable(x);
    ConstraintBlock block;
    block.name = "c";
    block.constraints.push_back(guarded);
    solver.AddConstraintBlock(block);

    ASSERT_TRUE(solver.Solve());
    EXPECT_GE(solver.GetValue("x"), 50);
    EXPECT_LE(solver.GetValue("x"), 60);
  }

  // mode == 0: the guard is FALSE, the range is eliminated and x ranges freely.
  {
    ConstraintSolver solver(99);
    RandVariable mode;
    mode.name = "mode";
    mode.min_val = 0;
    mode.max_val = 0;
    solver.AddVariable(mode);
    RandVariable x;
    x.name = "x";
    x.min_val = 0;
    x.max_val = 9;  // disjoint from the guarded range, provable only if dropped
    solver.AddVariable(x);
    ConstraintBlock block;
    block.name = "c";
    block.constraints.push_back(guarded);
    solver.AddConstraintBlock(block);

    ASSERT_TRUE(solver.Solve());
    EXPECT_GE(solver.GetValue("x"), 0);
    EXPECT_LE(solver.GetValue("x"), 9);
  }
}

// 18.5.12: both implication (->) and if...else may be used as guards. Each is
// an interdependent conditional constraint, and the four-state guard gates
// whether it is created. Here the consequent / then-set is unsatisfiable, so
// the constraint could only ever fail if generated; a FALSE guard eliminates
// it, and the solve succeeds with the variable left free.
TEST(ConstraintGuardSolver, ImplicationCanBeGuarded) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  // Antecedent always holds, so an unguarded implication would impose its
  // (unsatisfiable) consequent.
  impl.cond_fn = [](const Values&) { return true; };
  ConstraintExpr consequent;
  consequent.kind = ConstraintKind::kRange;
  consequent.var_name = "x";
  consequent.lo = 200;
  consequent.hi = 300;
  impl.sub_constraints.push_back(consequent);
  // The four-state guard gates creation of the whole implication.
  impl.has_guard = true;
  impl.guard = ConstantLeaf(GuardValue::kFalse);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 100);
}

// 18.5.12: an if...else constraint may likewise be used as a guard. With a TRUE
// guard the if...else is created and its then-set range is imposed on the
// solved value, showing the guard machinery applies to this construct too.
TEST(ConstraintGuardSolver, IfElseCanBeGuarded) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_fn = [](const Values&) { return true; };
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kRange;
  then_c.var_name = "x";
  then_c.lo = 70;
  then_c.hi = 80;
  ife.sub_constraints.push_back(then_c);
  ife.has_guard = true;
  ife.guard = ConstantLeaf(GuardValue::kTrue);
  block.constraints.push_back(ife);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 70);
  EXPECT_LE(solver.GetValue("x"), 80);
}

}  // namespace
