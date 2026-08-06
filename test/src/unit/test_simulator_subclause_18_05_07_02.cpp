#include <gtest/gtest.h>

#include <cstdint>
#include <string>
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

// A single-variable equality constraint used to pin an element to a value, so a
// reduction over the pinned elements is fully determined and observable.
ConstraintExpr Pin(const std::string& name, int64_t value) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = name;
  c.lo = value;
  return c;
}

// Build an array-reduction iterative constraint over the named element
// variables, comparing the fold against 'target' under 'cmp'.
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

// 18.5.7.2: in a constraint, a sum() reduction is treated as the elements
// joined by addition. This is the LRM example: A.sum() with (int'(item)) < 1000
// is interpreted as int'(A[0])+...+int'(A[4]) < 1000. With the five elements
// pinned to values whose sum is below 1000, the reduction holds and randomize()
// succeeds; the solver folds exactly those element values.
TEST(ArrayReductionConstraint, SumReductionJoinsElementsByAddition) {
  ConstraintSolver solver(42);
  const std::vector<std::string> kElems = {"e0", "e1", "e2", "e3", "e4"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255));

  ConstraintBlock pins;
  pins.name = "pins";
  const std::vector<int64_t> kVals = {100, 200, 50, 30, 20};  // sum 400 < 1000
  for (size_t i = 0; i < kElems.size(); ++i)
    pins.constraints.push_back(Pin(kElems[i], kVals[i]));
  solver.AddConstraintBlock(pins);

  // c2: A.sum() with (int'(item)) < 1000. int' of an in-range 8-bit value is
  // the value itself, so the with mapping is value-preserving; the 32-bit
  // result type leaves the sum un-truncated.
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

// 18.5.7.2: the reduction yields a single value that the relation must satisfy.
// When the folded sum violates the relation, randomization fails — the solver
// genuinely computes the reduction rather than ignoring it. Here the pinned
// elements sum to 1500, which is not < 1000.
TEST(ArrayReductionConstraint, ReductionViolationFailsRandomize) {
  ConstraintSolver solver(7);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 1000, 32));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 500));
  pins.constraints.push_back(Pin("e1", 500));
  pins.constraints.push_back(Pin("e2", 500));  // sum 1500
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                     ConstraintKind::kLessThan, 1000));
  solver.AddConstraintBlock(rc);

  EXPECT_FALSE(solver.Solve());
}

// 18.5.7.2: the with-clause expression is applied to each element before it is
// folded. Here the with expression squares each element (item*item), so the
// reduction of {1,2,3} is 1+4+9 == 14, observed by requiring the fold to equal
// that value.
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

  // A different target must fail, confirming the transform is what is folded.
  ConstraintSolver solver2(11);
  for (const auto& e : kElems) solver2.AddVariable(MakeVar(e, 0, 15, 8));
  solver2.AddConstraintBlock(pins);
  ConstraintExpr r2 = Reduction(ArrayReductionOp::kSum, kElems,
                                ConstraintKind::kEqual, 6);  // plain sum, wrong
  r2.reduce_with = [](int64_t item) { return item * item; };
  ConstraintBlock rc2;
  rc2.name = "reduce";
  rc2.constraints.push_back(r2);
  solver2.AddConstraintBlock(rc2);
  EXPECT_FALSE(solver2.Solve());
}

// 18.5.7.2: the result is of the array element type, or the with-clause
// expression type when specified. With an 8-bit element-type result, a sum that
// overflows 8 bits wraps (200+100 == 300 -> 44 mod 256); promoting the result
// to a 32-bit with-clause type (int'(item)) preserves the full sum (300). The
// two solves observe the result type governing the folded value.
TEST(ArrayReductionConstraint, ResultTypeGovernsTruncation) {
  const std::vector<std::string> kElems = {"e0", "e1"};

  // Element-type (8-bit) result: 300 truncates to 44.
  ConstraintSolver narrow(5);
  for (const auto& e : kElems) narrow.AddVariable(MakeVar(e, 0, 255, 8));
  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 200));
  pins.constraints.push_back(Pin("e1", 100));
  narrow.AddConstraintBlock(pins);
  ConstraintBlock nrc;
  nrc.name = "reduce";
  nrc.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                      ConstraintKind::kEqual, 44,
                                      /*result_width=*/8));
  narrow.AddConstraintBlock(nrc);
  EXPECT_TRUE(narrow.Solve());  // wraps to 44 in the 8-bit element type

  // The same fold against the full sum must fail under the 8-bit result type.
  ConstraintSolver narrow2(5);
  for (const auto& e : kElems) narrow2.AddVariable(MakeVar(e, 0, 255, 8));
  narrow2.AddConstraintBlock(pins);
  ConstraintBlock nrc2;
  nrc2.name = "reduce";
  nrc2.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                       ConstraintKind::kEqual, 300,
                                       /*result_width=*/8));
  narrow2.AddConstraintBlock(nrc2);
  EXPECT_FALSE(narrow2.Solve());

  // with (int'(item)): a 32-bit result type preserves the full sum 300.
  ConstraintSolver wide(5);
  for (const auto& e : kElems) wide.AddVariable(MakeVar(e, 0, 255, 8));
  wide.AddConstraintBlock(pins);
  ConstraintBlock wrc;
  wrc.name = "reduce";
  wrc.constraints.push_back(Reduction(ArrayReductionOp::kSum, kElems,
                                      ConstraintKind::kEqual, 300,
                                      /*result_width=*/32));
  wide.AddConstraintBlock(wrc);
  EXPECT_TRUE(wide.Solve());  // full sum survives in the wider with-clause type
}

// 18.5.7.2: "the relevant operand for each method" — a product() reduction
// joins the elements by multiplication. {2,3,4} folds to 24.
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

  // A different target must fail, confirming the multiplicative fold is what is
  // computed rather than any other join (e.g. a sum would give 9).
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

// 18.5.7.2: "the relevant operand for each method" — an and() reduction joins
// the elements by bitwise AND. {0xFF, 0x0F, 0x3C} folds to 0x0C. The all-ones
// identity means a fold over the listed elements leaves only the bits common to
// all of them set.
TEST(ArrayReductionConstraint, AndReductionJoinsByBitwiseAnd) {
  ConstraintSolver solver(21);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 8));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 0xFF));
  pins.constraints.push_back(Pin("e1", 0x0F));
  pins.constraints.push_back(Pin("e2", 0x3C));  // 0xFF & 0x0F & 0x3C == 0x0C
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(
      Reduction(ArrayReductionOp::kAnd, kElems, ConstraintKind::kEqual, 0x0C));
  solver.AddConstraintBlock(rc);

  EXPECT_TRUE(solver.Solve());

  // A different target must fail, confirming the AND fold is what is computed.
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

// 18.5.7.2: "the relevant operand for each method" — an or() reduction joins
// the elements by bitwise OR. {0x01, 0x02, 0x04} folds to 0x07.
TEST(ArrayReductionConstraint, OrReductionJoinsByBitwiseOr) {
  ConstraintSolver solver(22);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 8));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 0x01));
  pins.constraints.push_back(Pin("e1", 0x02));
  pins.constraints.push_back(Pin("e2", 0x04));  // 0x01 | 0x02 | 0x04 == 0x07
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(
      Reduction(ArrayReductionOp::kOr, kElems, ConstraintKind::kEqual, 0x07));
  solver.AddConstraintBlock(rc);

  EXPECT_TRUE(solver.Solve());

  // A different target must fail, confirming the OR fold is what is computed
  // (a sum of the same elements would also give 0x07, so pick a value neither
  // join reaches to pin the bitwise-OR result specifically).
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

// 18.5.7.2: "the relevant operand for each method" — an xor() reduction joins
// the elements by bitwise XOR. {0x0F, 0x03, 0x01} folds to 0x0D, and the zero
// identity makes an even pairing of a bit cancel out.
TEST(ArrayReductionConstraint, XorReductionJoinsByBitwiseXor) {
  ConstraintSolver solver(23);
  const std::vector<std::string> kElems = {"e0", "e1", "e2"};
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 8));

  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 0x0F));
  pins.constraints.push_back(Pin("e1", 0x03));
  pins.constraints.push_back(Pin("e2", 0x01));  // 0x0F ^ 0x03 ^ 0x01 == 0x0D
  solver.AddConstraintBlock(pins);

  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(
      Reduction(ArrayReductionOp::kXor, kElems, ConstraintKind::kEqual, 0x0D));
  solver.AddConstraintBlock(rc);

  EXPECT_TRUE(solver.Solve());

  // A different target must fail, confirming the XOR fold is what is computed
  // rather than, e.g., an OR (which would give 0x0F for these elements).
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

// 18.5.7.2: as with foreach iterative constraints, when an array has both size
// constraints and array-reduction iterative constraints the size is solved
// first and the reduction next, so only the elements that exist take part. The
// size is pinned to 2, so the reduction folds only e0 and e1 (sum 30 < 100)
// even though the trailing elements carry large values; folding all four would
// give 540 and the < 100 relation would fail.
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
  pins.constraints.push_back(Pin("e1", 20));   // existing: sum 30
  pins.constraints.push_back(Pin("e2", 255));  // beyond size 2
  pins.constraints.push_back(Pin("e3", 255));  // beyond size 2
  solver.AddConstraintBlock(pins);

  ConstraintExpr r =
      Reduction(ArrayReductionOp::kSum, kElems, ConstraintKind::kLessThan, 100);
  r.size_var = "n";  // dynamically sized: size committed before the reduction
  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(r);
  solver.AddConstraintBlock(rc);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 2);
  EXPECT_EQ(solver.GetValue("e0"), 10);
  EXPECT_EQ(solver.GetValue("e1"), 20);
}

// 18.5.7.2: size is solved before the iterative constraint, so when the array's
// size resolves to zero the reduction iterates over no elements. The fold then
// returns the operand's identity (zero for sum); the elements beyond the
// committed size carry large values yet take no part. A sum() == 0 constraint
// therefore holds, while demanding a nonzero sum fails — confirming the empty
// fold is what production computes rather than folding the out-of-bounds tail.
TEST(ArrayReductionConstraint, EmptyReductionYieldsOperatorIdentity) {
  const std::vector<std::string> kElems = {"e0", "e1"};
  ConstraintBlock pins;
  pins.name = "pins";
  pins.constraints.push_back(Pin("e0", 255));  // beyond size 0
  pins.constraints.push_back(Pin("e1", 255));  // beyond size 0

  ConstraintSolver solver(3);
  RandVariable n = MakeVar("n", 0, 0, 32);
  n.is_array_size = true;
  solver.AddVariable(n);
  for (const auto& e : kElems) solver.AddVariable(MakeVar(e, 0, 255, 32));
  solver.AddConstraintBlock(pins);
  ConstraintExpr r =
      Reduction(ArrayReductionOp::kSum, kElems, ConstraintKind::kEqual, 0);
  r.size_var = "n";  // dynamically sized: size committed before the reduction
  ConstraintBlock rc;
  rc.name = "reduce";
  rc.constraints.push_back(r);
  solver.AddConstraintBlock(rc);
  ASSERT_TRUE(solver.Solve());  // empty fold == 0 (sum identity)
  EXPECT_EQ(solver.GetValue("n"), 0);

  // Requiring a strictly positive sum must fail: no element is folded.
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
