#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// A plain integral rand variable over [lo, hi] with the given bit width.
RandVariable MakeVar(const std::string& name, int64_t lo, int64_t hi,
                     uint32_t width = 8) {
  RandVariable v;
  v.name = name;
  v.min_val = lo;
  v.max_val = hi;
  v.width = width;
  return v;
}

// A membership constraint 'var inside set', referencing only 'var'. The
// reference list lets the function-argument priority solve enforce it as soon as
// 'var' is committed.
ConstraintExpr InsideSet(const std::string& var, std::vector<int64_t> set) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = var;
  c.set_values = std::move(set);
  c.ref_vars = {var};
  return c;
}

// A custom relation over the current values, standing in for a constraint whose
// right-hand side is a function call. 'refs' names the random variables the
// relation reads, so the priority solve defers it until they are all committed.
ConstraintExpr Custom(
    std::vector<std::string> refs,
    std::function<bool(const std::unordered_map<std::string, int64_t>&)> fn) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kCustom;
  c.ref_vars = std::move(refs);
  c.eval_fn = std::move(fn);
  return c;
}

ConstraintBlock OneBlock(std::vector<ConstraintExpr> cs) {
  ConstraintBlock b;
  b.name = "c";
  b.constraints = std::move(cs);
  return b;
}

// 18.5.11: a random variable used as a function argument becomes a state
// variable to the constraint that uses it. With y solved first (it is the
// argument) the constraint x == 2*F(y) sees y as a fixed value: here y is pinned
// to 2, so x is forced to 4. The function result (2*y) acts as a constant once y
// is committed.
TEST(FunctionsInConstraints, FunctionArgumentVariableIsStateVariableToConsumer) {
  ConstraintSolver solver(101);
  solver.AddVariable(MakeVar("y", 2, 2));  // pinned argument value
  solver.AddVariable(MakeVar("x", 0, 7));
  solver.AddConstraintBlock(OneBlock({Custom({"x", "y"}, [](const auto& v) {
    return v.at("x") == 2 * v.at("y");
  })}));
  // Using y as a function argument gives it higher priority than x.
  solver.AddFunctionArgPriority({"y"}, {"x"});
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("y"), 2);
  EXPECT_EQ(solver.GetValue("x"), 4);
}

// 18.5.11: the argument variable is solved against only its own (higher
// priority) constraints; the consumer's constraint is honored afterward with the
// argument already chosen. Over many solves y always lands in its own legal set
// and x always satisfies the relation built on F(y).
TEST(FunctionsInConstraints, ArgumentSolvedFirstThenConsumerConstraintHolds) {
  ConstraintSolver solver(202);
  solver.AddVariable(MakeVar("y", 0, 8));
  solver.AddVariable(MakeVar("x", 0, 16));
  solver.AddConstraintBlock(OneBlock({
      InsideSet("y", {2, 4, 8}),
      // x <= 2*F(y); the right-hand side reads y as a state variable.
      Custom({"x", "y"},
             [](const auto& v) { return v.at("x") <= 2 * v.at("y"); }),
  }));
  solver.AddFunctionArgPriority({"y"}, {"x"});
  for (int i = 0; i < 200; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t y = solver.GetValue("y");
    int64_t x = solver.GetValue("x");
    EXPECT_TRUE(y == 2 || y == 4 || y == 8);
    EXPECT_LE(x, 2 * y);
  }
}

// 18.5.11: priorities chain. When the constraint on x uses y as an argument and
// the constraint on y uses z as an argument, z is highest priority, then y, then
// x. Each is solved before the variable that consumes it, so the committed
// upstream value flows down: z = 2 forces y = 3, which forces x = 4.
TEST(FunctionsInConstraints, ChainedPriorityOrdersThreeVariables) {
  ConstraintSolver solver(303);
  solver.AddVariable(MakeVar("z", 2, 2));  // pinned source value
  solver.AddVariable(MakeVar("y", 0, 7));
  solver.AddVariable(MakeVar("x", 0, 7));
  solver.AddConstraintBlock(OneBlock({
      Custom({"y", "z"}, [](const auto& v) { return v.at("y") == v.at("z") + 1; }),
      Custom({"x", "y"}, [](const auto& v) { return v.at("x") == v.at("y") + 1; }),
  }));
  solver.AddFunctionArgPriority({"z"}, {"y"});
  solver.AddFunctionArgPriority({"y"}, {"x"});
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("z"), 2);
  EXPECT_EQ(solver.GetValue("y"), 3);
  EXPECT_EQ(solver.GetValue("x"), 4);
}

// 18.5.11: a circular dependency created by the implicit variable ordering shall
// result in an error. Using a in a constraint on b and b in a constraint on a
// makes each higher priority than the other; randomize() fails outright rather
// than solving a self-contradictory ordering.
TEST(FunctionsInConstraints, CircularImplicitPriorityFailsRandomize) {
  ConstraintSolver solver(404);
  solver.AddVariable(MakeVar("a", 0, 7));
  solver.AddVariable(MakeVar("b", 0, 7));
  solver.AddConstraintBlock(OneBlock({
      Custom({"a", "b"}, [](const auto& v) { return v.at("a") <= v.at("b"); }),
      Custom({"a", "b"}, [](const auto& v) { return v.at("b") <= v.at("a"); }),
  }));
  solver.AddFunctionArgPriority({"a"}, {"b"});  // a before b
  solver.AddFunctionArgPriority({"b"}, {"a"});  // and b before a -> cycle
  EXPECT_FALSE(solver.Solve());
}

// 18.5.11: within a prioritized set the cyclical (randc) variables are solved
// first. A randc variable committed ahead of the priority-ordered rand variables
// keeps its no-repeat cyclic behavior: across one full iteration it visits every
// value in its domain exactly once, even while a function-argument priority
// orders the rand variables alongside it.
TEST(FunctionsInConstraints, RandcSolvedFirstWithinPrioritizedSet) {
  ConstraintSolver solver(505);
  RandVariable c = MakeVar("c", 0, 3, 2);
  c.qualifier = RandQualifier::kRandc;
  solver.AddVariable(c);
  solver.AddVariable(MakeVar("y", 0, 7));
  solver.AddVariable(MakeVar("x", 0, 16));
  solver.AddConstraintBlock(OneBlock({
      InsideSet("y", {1, 2, 3}),
      Custom({"x", "y"}, [](const auto& v) { return v.at("x") <= 2 * v.at("y"); }),
  }));
  solver.AddFunctionArgPriority({"y"}, {"x"});
  std::vector<int> counts(4, 0);
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(solver.Solve());
    counts[solver.GetValue("c")]++;
    EXPECT_LE(solver.GetValue("x"), 2 * solver.GetValue("y"));
  }
  // One complete randc iteration visits each of the four values exactly once.
  for (int v = 0; v < 4; ++v) EXPECT_EQ(counts[v], 1);
}

// 18.5.11: with no function-argument priority recorded the solver keeps its
// ordinary flat behavior — the new layered path is inert unless a priority edge
// applies. The same constraints solve directly.
TEST(FunctionsInConstraints, NoPriorityEdgesLeavesFlatSolveUnchanged) {
  ConstraintSolver solver(606);
  solver.AddVariable(MakeVar("x", 0, 7));
  solver.AddVariable(MakeVar("y", 0, 7));
  solver.AddConstraintBlock(OneBlock({
      Custom({"x", "y"}, [](const auto& v) { return v.at("x") == v.at("y"); }),
  }));
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), solver.GetValue("y"));
}

// 18.5.11: more than one variable may share a priority. When a constraint uses
// two variables as function arguments, both are higher priority than the
// consumer and are gathered into the first layer, solved before it. Here y and z
// are committed first and x == F(y) + G(z) sees both as state variables.
TEST(FunctionsInConstraints, MultipleArgumentsShareOnePriorityLayer) {
  ConstraintSolver solver(707);
  solver.AddVariable(MakeVar("y", 2, 2));  // pinned argument values
  solver.AddVariable(MakeVar("z", 3, 3));
  solver.AddVariable(MakeVar("x", 0, 7));
  solver.AddConstraintBlock(OneBlock({Custom({"x", "y", "z"}, [](const auto& v) {
    return v.at("x") == v.at("y") + v.at("z");
  })}));
  solver.AddFunctionArgPriority({"y"}, {"x"});
  solver.AddFunctionArgPriority({"z"}, {"x"});
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("y"), 2);
  EXPECT_EQ(solver.GetValue("z"), 3);
  EXPECT_EQ(solver.GetValue("x"), 5);
}

// 18.5.11: the higher-priority variables are solved against only their own
// constraints, with no reconsideration once committed. If a higher-priority
// variable's own constraints admit no value, that layer cannot be completed and
// randomize() fails — the subdivision into priorities can make the solve fail.
TEST(FunctionsInConstraints, UnsatisfiableHigherPriorityLayerFailsSolve) {
  ConstraintSolver solver(808);
  solver.AddVariable(MakeVar("y", 0, 7));
  solver.AddVariable(MakeVar("x", 0, 7));
  solver.AddConstraintBlock(OneBlock({
      // y's own constraints are mutually exclusive, so the highest-priority
      // layer can never be satisfied.
      Custom({"y"}, [](const auto& v) { return v.at("y") > 5; }),
      Custom({"y"}, [](const auto& v) { return v.at("y") < 2; }),
      Custom({"x", "y"}, [](const auto& v) { return v.at("x") == v.at("y"); }),
  }));
  solver.AddFunctionArgPriority({"y"}, {"x"});
  EXPECT_FALSE(solver.Solve());
}

}  // namespace
