#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_map>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

using Values = std::unordered_map<std::string, int64_t>;

GuardPredicate ConstantLeaf(GuardValue v) {
  GuardPredicate leaf;
  leaf.op = GuardPredicate::Op::kLeaf;
  leaf.leaf_fn = [v](const Values&) { return v; };
  return leaf;
}

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

TEST(ConstraintGuard4State, NegationTruthTable) {
  EXPECT_EQ(GuardNot(GuardValue::kFalse), GuardValue::kTrue);
  EXPECT_EQ(GuardNot(GuardValue::kTrue), GuardValue::kFalse);
  EXPECT_EQ(GuardNot(GuardValue::kError), GuardValue::kError);
  EXPECT_EQ(GuardNot(GuardValue::kRandom), GuardValue::kRandom);
}

TEST(ConstraintGuard4State, FinalOutcomeMapping) {
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kTrue), GuardOutcome::kUnconditional);
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kFalse), GuardOutcome::kEliminated);
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kError), GuardOutcome::kError);
  EXPECT_EQ(GuardFinalOutcome(GuardValue::kRandom), GuardOutcome::kConditional);
}

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

TEST(ConstraintGuardTree, MissingLeafIsError) {
  GuardPredicate leaf;
  EXPECT_EQ(EvaluateGuard(leaf, Values{}), GuardValue::kError);
}

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

TEST(ConstraintGuardSolver, RandomGuardGeneratesConstraint) {
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
  guarded.lo = 30;
  guarded.hi = 40;
  guarded.has_guard = true;
  guarded.guard = ConstantLeaf(GuardValue::kRandom);
  block.constraints.push_back(guarded);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 30);
  EXPECT_LE(solver.GetValue("x"), 40);
}

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
    x.max_val = 9;
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
  impl.cond_fn = [](const Values&) { return true; };
  ConstraintExpr consequent;
  consequent.kind = ConstraintKind::kRange;
  consequent.var_name = "x";
  consequent.lo = 200;
  consequent.hi = 300;
  impl.sub_constraints.push_back(consequent);
  impl.has_guard = true;
  impl.guard = ConstantLeaf(GuardValue::kFalse);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 100);
}

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
