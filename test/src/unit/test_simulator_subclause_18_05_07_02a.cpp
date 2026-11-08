#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

RandVariable MakeVar(const std::string& name, int64_t lo, int64_t hi,
                     uint32_t width = 8) {
  RandVariable v;
  v.name = name;
  v.min_val = lo;
  v.max_val = hi;
  v.width = width;
  return v;
}

ConstraintExpr Pin(const std::string& name, int64_t value) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = name;
  c.lo = value;
  return c;
}

ConstraintExpr Reduction(ArrayReductionOp op,
                         const std::vector<std::string>& vars,
                         ConstraintKind cmp, int64_t target,
                         uint32_t result_width = 32) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kArrayReduction;
  c.reduce_op = op;
  c.reduce_vars = vars;
  c.reduce_cmp = cmp;
  c.lo = target;
  c.reduce_width = result_width;
  return c;
}

TEST(ArrayReductionConstraint, SumReductionJoinsElementsByAddition) {
  ConstraintSolver solver(42);
  const std::vector<std::string> kElems = {"e0", "e1", "e2", "e3", "e4"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255));

  ConstraintBlock pins;
  pins.name = "pins";
  const std::vector<int64_t> kVals = {100, 200, 50, 30, 20};
  for (size_t i = 0; i < kElems.size(); ++i)
    pins.constraints.push_back(Pin(kElems[i], kVals[i]));
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                     ConstraintKind::kLessThan, 1000));
  solver.AddConstraintBlock(rc);

  ASSERT_TRUE(solver.Solve());
  int64_t sum = 0;
  for (const auto& e : kElems) sum += solver.GetValue(e);
  EXPECT_EQ(sum, 400);
  EXPECT_LT(sum, 1000);
}

TEST(ArrayReductionConstraint, ReductionViolationFailsRandomize) {
  ConstraintSolver solver(7);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 1000, 32));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 500));
  pins.constraints.push_back(Pin("e1", 500));
  pins.constraints.push_back(Pin("e2", 500));
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                     ConstraintKind::kLessThan, 1000));
  solver.AddConstraintBlock(rc);

  EXPECT_FALSE(solver.Solve());
}

TEST(ArrayReductionConstraint, WithClauseExpressionTransformsEachElement) {
  ConstraintSolver solver(11);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 15, 8));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 1));
  pins.constraints.push_back(Pin("e1", 2));
  pins.constraints.push_back(Pin("e2", 3));
  solver.AddConstraintBlock(pins);

  ConstraintExpr r =
      Reduction(ArrayReductionOp::kSum, kElems, ConstraintKind::kEqual, 14);
  r.reduce_with = [](int64_t item) { return item * item; };
  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(r);
  solver.AddConstraintBlock(rc);

  ASSERT_TRUE(solver.Solve());

  ConstraintSolver solver2(11);
  for (const auto& e : kElems) solver2.AddVariable(MakeVar(e, 0, 15, 8));
  solver2.AddConstraintBlock(pins);
  ConstraintExpr r2 =
      Reduction(ArrayReductionOp::kSum, kElems, ConstraintKind::kEqual, 6);
  r2.reduce_with = [](int64_t item) { return item * item; };
  ConstraintBlock rc2;
  rc2.name = "reduce";
  rc2.constraints.push_back(r2);
  solver2.AddConstraintBlock(rc2);
  EXPECT_FALSE(solver2.Solve());
}

TEST(ArrayReductionConstraint, ResultTypeGovernsTruncation) {
  const std::vector<std::string> kElems = {"e0", "e1"};

  ConstraintSolver narrow(5);
  for (const auto& e : kElems) narrow.AddVariable(MakeVar(e, 0, 255, 8));
  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 200));
  pins.constraints.push_back(Pin("e1", 100));
  narrow.AddConstraintBlock(pins);
  ConstraintBlock nrc;
  nrc.name = "reduce";
  nrc.constraints.push_back(
      Reduction(ArrayReductionOp::kSum, kElems, ConstraintKind::kEqual, 44, 8));
  narrow.AddConstraintBlock(nrc);
  EXPECT_TRUE(narrow.Solve());

  ConstraintSolver narrow2(5);
  for (const auto& e : kElems) narrow2.AddVariable(MakeVar(e, 0, 255, 8));
  narrow2.AddConstraintBlock(pins);
  ConstraintBlock nrc2;
  nrc2.name = "reduce";
  nrc2.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                       ConstraintKind::kEqual, 300, 8));
  narrow2.AddConstraintBlock(nrc2);
  EXPECT_FALSE(narrow2.Solve());

  ConstraintSolver wide(5);
  for (const auto& e : kElems) wide.AddVariable(MakeVar(e, 0, 255, 8));
  wide.AddConstraintBlock(pins);
  ConstraintBlock wrc;
  wrc.name = "reduce";
  wrc.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                      ConstraintKind::kEqual, 300, 32));
  wide.AddConstraintBlock(wrc);
  EXPECT_TRUE(wide.Solve());
}

TEST(ArrayReductionConstraint, ProductReductionJoinsByMultiplication) {
  ConstraintSolver solver(13);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 32));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 2));
  pins.constraints.push_back(Pin("e1", 3));
  pins.constraints.push_back(Pin("e2", 4));
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(Reduction(ArrayReductionOp::kProduct, kElems,
                                     ConstraintKind::kEqual, 24));
  solver.AddConstraintBlock(rc);

  EXPECT_TRUE(solver.Solve());

  ConstraintSolver solver2(13);
  for (const auto& e : kElems) solver2.AddVariable(MakeVar(e, 0, 255, 32));
  solver2.AddConstraintBlock(pins);
  ConstraintBlock rc2;
  rc2.name = "reduce";
  rc2.constraints.push_back(
      Reduction(ArrayReductionOp::kProduct, kElems, ConstraintKind::kEqual, 9));
  solver2.AddConstraintBlock(rc2);
  EXPECT_FALSE(solver2.Solve());
}

TEST(ArrayReductionConstraint, AndReductionJoinsByBitwiseAnd) {
  ConstraintSolver solver(21);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 8));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 0xFF));
  pins.constraints.push_back(Pin("e1", 0x0F));
  pins.constraints.push_back(Pin("e2", 0x3C));
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(
      Reduction(ArrayReductionOp::kAnd, kElems, ConstraintKind::kEqual, 0x0C));
  solver.AddConstraintBlock(rc);

  EXPECT_TRUE(solver.Solve());

  ConstraintSolver solver2(21);
  for (const auto& e : kElems) solver2.AddVariable(MakeVar(e, 0, 255, 8));
  solver2.AddConstraintBlock(pins);
  ConstraintBlock rc2;
  rc2.name = "reduce";
  rc2.constraints.push_back(
      Reduction(ArrayReductionOp::kAnd, kElems, ConstraintKind::kEqual, 0x0F));
  solver2.AddConstraintBlock(rc2);
  EXPECT_FALSE(solver2.Solve());
}

TEST(ArrayReductionConstraint, OrReductionJoinsByBitwiseOr) {
  ConstraintSolver solver(22);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 8));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 0x01));
  pins.constraints.push_back(Pin("e1", 0x02));
  pins.constraints.push_back(Pin("e2", 0x04));
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(
      Reduction(ArrayReductionOp::kOr, kElems, ConstraintKind::kEqual, 0x07));
  solver.AddConstraintBlock(rc);

  EXPECT_TRUE(solver.Solve());

  ConstraintSolver solver2(22);
  for (const auto& e : kElems) solver2.AddVariable(MakeVar(e, 0, 255, 8));
  solver2.AddConstraintBlock(pins);
  ConstraintBlock rc2;
  rc2.name = "reduce";
  rc2.constraints.push_back(
      Reduction(ArrayReductionOp::kOr, kElems, ConstraintKind::kEqual, 0x06));
  solver2.AddConstraintBlock(rc2);
  EXPECT_FALSE(solver2.Solve());
}

TEST(ArrayReductionConstraint, XorReductionJoinsByBitwiseXor) {
  ConstraintSolver solver(23);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 8));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 0x0F));
  pins.constraints.push_back(Pin("e1", 0x03));
  pins.constraints.push_back(Pin("e2", 0x01));
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(
      Reduction(ArrayReductionOp::kXor, kElems, ConstraintKind::kEqual, 0x0D));
  solver.AddConstraintBlock(rc);

  EXPECT_TRUE(solver.Solve());

  ConstraintSolver solver2(23);
  for (const auto& e : kElems) solver2.AddVariable(MakeVar(e, 0, 255, 8));
  solver2.AddConstraintBlock(pins);
  ConstraintBlock rc2;
  rc2.name = "reduce";
  rc2.constraints.push_back(
      Reduction(ArrayReductionOp::kXor, kElems, ConstraintKind::kEqual, 0x0F));
  solver2.AddConstraintBlock(rc2);
  EXPECT_FALSE(solver2.Solve());
}

TEST(ArrayReductionConstraint, SizeConstraintBoundsReduction) {
  ConstraintSolver solver(99);
  RandVariable n = MakeVar("n", 2, 2, 32);
  n.is_array_size = true;
  solver.AddVariable(n);
  const std::vector<std::string> kElems = {"e0", "e1", "e2", "e3"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 32));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 10));
  pins.constraints.push_back(Pin("e1", 20));
  pins.constraints.push_back(Pin("e2", 255));
  pins.constraints.push_back(Pin("e3", 255));
  solver.AddConstraintBlock(pins);

  ConstraintExpr r =
      Reduction(ArrayReductionOp::kSum, kElems, ConstraintKind::kLessThan, 100);
  r.size_var = "n";
  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(r);
  solver.AddConstraintBlock(rc);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 2);
  EXPECT_EQ(solver.GetValue("e0"), 10);
  EXPECT_EQ(solver.GetValue("e1"), 20);
}

TEST(ArrayReductionConstraint, EmptyReductionYieldsOperatorIdentity) {
  const std::vector<std::string> kElems = {"e0", "e1"};
  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 255));
  pins.constraints.push_back(Pin("e1", 255));

  ConstraintSolver solver(3);
  RandVariable n = MakeVar("n", 0, 0, 32);
  n.is_array_size = true;
  solver.AddVariable(n);
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 32));
  solver.AddConstraintBlock(pins);
  ConstraintExpr r =
      Reduction(ArrayReductionOp::kSum, kElems, ConstraintKind::kEqual, 0);
  r.size_var = "n";
  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(r);
  solver.AddConstraintBlock(rc);
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 0);

  ConstraintSolver solver2(3);
  RandVariable n2 = MakeVar("n", 0, 0, 32);
  n2.is_array_size = true;
  solver2.AddVariable(n2);
  for (const auto& e : kElems) solver2.AddVariable(MakeVar(e, 0, 255, 32));
  solver2.AddConstraintBlock(pins);
  ConstraintExpr r2 = Reduction(ArrayReductionOp::kSum, kElems,
                                ConstraintKind::kGreaterThan, 0);
  r2.size_var = "n";
  ConstraintBlock rc2;
  rc2.name = "reduce";
  rc2.constraints.push_back(r2);
  solver2.AddConstraintBlock(rc2);
  EXPECT_FALSE(solver2.Solve());
}

}  // namespace
