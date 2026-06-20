#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

TEST(Constraint, InsideSetMembership) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "mode";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_inside";
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = "mode";
  c.set_values = {1, 5, 10, 50};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("mode");
  EXPECT_TRUE(val == 1 || val == 5 || val == 10 || val == 50);
}

TEST(Constraint, InsideSetSingleValue) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_single";
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = "x";
  c.set_values = {77};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 77);
}

// Build a solver holding one variable "x" over [lo, hi] constrained by a single
// dist with the given weighted set, then sample it `runs` times and return the
// list of solved values.
std::vector<int64_t> SampleDist(int64_t lo, int64_t hi,
                                const std::vector<DistWeight>& weights,
                                int runs,
                                RandQualifier q = RandQualifier::kRand) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = lo;
  v.max_val = hi;
  v.qualifier = q;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_dist";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "x";
  c.dist_weights = weights;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  std::vector<int64_t> out;
  for (int i = 0; i < runs; ++i) {
    if (!solver.Solve()) break;
    out.push_back(solver.GetValue("x"));
  }
  return out;
}

DistWeight Single(int64_t value, uint32_t weight) {
  DistWeight w;
  w.value = value;
  w.weight = weight;
  return w;
}

DistWeight Range(int64_t lo, int64_t hi, uint32_t weight, bool per_element) {
  DistWeight w;
  w.weight = weight;
  w.lo = lo;
  w.hi = hi;
  w.is_range = true;
  w.per_element = per_element;
  return w;
}

int Count(const std::vector<int64_t>& vals, int64_t target) {
  return static_cast<int>(std::count(vals.begin(), vals.end(), target));
}

int CountInRange(const std::vector<int64_t>& vals, int64_t lo, int64_t hi) {
  int n = 0;
  for (int64_t v : vals)
    if (v >= lo && v <= hi) ++n;
  return n;
}

// 18.5.3: absent any other constraints, the probability that the expression
// matches an item shall be proportional to that item's weight. A 1000:1 weight
// ratio drives almost every sample to the heavily weighted value.
TEST(ConstraintDist, ProbabilityProportionalToWeight) {
  auto vals = SampleDist(0, 100, {Single(10, 1000), Single(20, 1)}, 200);
  ASSERT_EQ(vals.size(), 200u);
  EXPECT_GT(Count(vals, 10), 180);
  EXPECT_LT(Count(vals, 20), 20);
}

// 18.5.3: a distribution is a relational test for set membership, so only
// values named by the dist set are ever produced; the rest of the domain is
// excluded.
TEST(ConstraintDist, OnlyListedValuesProduced) {
  auto vals =
      SampleDist(0, 100, {Single(10, 1), Single(20, 1), Single(30, 1)}, 200);
  ASSERT_EQ(vals.size(), 200u);
  for (int64_t v : vals) EXPECT_TRUE(v == 10 || v == 20 || v == 30);
}

// 18.5.3: when := is applied to a range the weight is assigned to each element,
// so a four-element range with weight 1 is four times as likely overall as a
// single value with weight 1.
TEST(ConstraintDist, AssignWeightOnRangeIsPerElement) {
  auto vals = SampleDist(0, 100, {Range(0, 3, 1, true), Single(10, 1)}, 400);
  ASSERT_EQ(vals.size(), 400u);
  int in_range = CountInRange(vals, 0, 3);
  int at_ten = Count(vals, 10);
  // Expected ratio is 4:1; require the range to dominate by a clear margin.
  EXPECT_GT(in_range, at_ten * 2);
}

// 18.5.3: when :/ is applied to a range the weight is assigned to the range as
// a whole, so the same four-element range with weight 1 is only as likely
// overall as a single value with weight 1.
TEST(ConstraintDist, DivideWeightOnRangeIsWholeRange) {
  auto vals = SampleDist(0, 100, {Range(0, 3, 1, false), Single(10, 1)}, 400);
  ASSERT_EQ(vals.size(), 400u);
  int in_range = CountInRange(vals, 0, 3);
  int at_ten = Count(vals, 10);
  // Expected ratio is 1:1; both outcomes should be of comparable frequency.
  EXPECT_GT(in_range, at_ten / 2);
  EXPECT_GT(at_ten, in_range / 2);
}

// 18.5.3: if a single value occurs in multiple items, the weights allocated to
// that value are additive. Value 200 appears in two weight-1 items and so is
// about twice as likely as the single weight-1 value 100.
TEST(ConstraintDist, WeightsAreAdditiveAcrossItems) {
  auto vals =
      SampleDist(0, 100, {Single(100, 1), Single(200, 1), Single(200, 1)}, 300);
  ASSERT_EQ(vals.size(), 300u);
  EXPECT_GT(Count(vals, 200), Count(vals, 100));
}

// 18.5.3: the additive behavior includes items explicitly weighted to zero. The
// 100:/0 item does not exclude 100 because 100 is also covered by a nonzero
// range item, so all of 100, 101, 102 remain reachable.
TEST(ConstraintDist, ZeroWeightItemDoesNotConstrainWhenCoveredElsewhere) {
  std::vector<DistWeight> weights = {Single(100, 0), Range(100, 102, 1, false)};
  auto vals = SampleDist(0, 200, weights, 300);
  ASSERT_EQ(vals.size(), 300u);
  for (int64_t v : vals) EXPECT_TRUE(v >= 100 && v <= 102);
  EXPECT_GT(Count(vals, 100), 0);
  EXPECT_GT(Count(vals, 101), 0);
  EXPECT_GT(Count(vals, 102), 0);
}

// 18.5.3: the default specification stands for every value of the domain not
// present in any other item. With [0:1] named explicitly, a default draw lands
// on a value from the complement {2, 3, 4} of the [0:4] domain.
TEST(ConstraintDist, DefaultCoversRemainderOfDomain) {
  DistWeight def;
  def.weight = 1;
  def.is_default = true;
  auto vals = SampleDist(0, 4, {Range(0, 1, 1, false), def}, 300);
  ASSERT_EQ(vals.size(), 300u);
  for (int64_t v : vals) EXPECT_TRUE(v >= 0 && v <= 4);
  // The default item is reachable, so values outside [0:1] must occur.
  EXPECT_GT(CountInRange(vals, 2, 4), 0);
}

// 18.5.3: a dist operation shall not be applied to a randc variable, so a
// distribution targeting one makes randomization fail.
TEST(ConstraintDist, DistOnRandcVariableFails) {
  auto vals = SampleDist(0, 100, {Single(10, 1), Single(20, 1)}, 1,
                         RandQualifier::kRandc);
  EXPECT_TRUE(vals.empty());
}

// 18.5.3: a dist expression requires that the expression contain at least one
// rand variable. A distribution applied to a variable with no rand qualifier
// supplies no rand variable to the expression, so randomization fails.
TEST(ConstraintDist, DistRequiresRandVariableFails) {
  auto vals = SampleDist(0, 100, {Single(10, 1), Single(20, 1)}, 1,
                         RandQualifier::kNone);
  EXPECT_TRUE(vals.empty());
}

// 18.5.3 (control): the same distribution applied to a rand variable solves
// successfully and yields one of the listed values.
TEST(ConstraintDist, DistOnRandVariableSolves) {
  auto vals = SampleDist(0, 100, {Single(10, 1), Single(20, 1)}, 1,
                         RandQualifier::kRand);
  ASSERT_EQ(vals.size(), 1u);
  EXPECT_TRUE(vals[0] == 10 || vals[0] == 20);
}

// 18.5.3: an integral item with no weight specified takes a default weight of
// 1. Here the value 100 is given no explicit weight and the value 200 is given
// weight 1; the two should therefore occur with comparable frequency.
TEST(ConstraintDist, AbsentWeightDefaultsToOne) {
  DistWeight no_weight;
  no_weight.value = 100;  // weight left at its default of 1
  auto vals = SampleDist(0, 100, {no_weight, Single(200, 1)}, 300);
  ASSERT_EQ(vals.size(), 300u);
  int at_100 = Count(vals, 100);
  int at_200 = Count(vals, 200);
  EXPECT_GT(at_100, at_200 / 2);
  EXPECT_GT(at_200, at_100 / 2);
}

// 18.5.3: the weight is interpreted as an unsigned value. A weight whose most
// significant bit is set — a negative number if it were read as a signed
// quantity — is honoured as a large positive magnitude, so the value carrying
// it overwhelms a value weighted 1 rather than dropping out of the draw.
TEST(ConstraintDist, WeightInterpretedAsUnsigned) {
  auto vals = SampleDist(0, 100, {Single(10, 0x80000000u), Single(20, 1)}, 200);
  ASSERT_EQ(vals.size(), 200u);
  EXPECT_GT(Count(vals, 10), 195);
  EXPECT_LT(Count(vals, 20), 5);
}

// 18.5.3: both the := and :/ operators assign the specified weight to an
// individual value, so for single values the two operators are equivalent.
// Built from identical values and weights against the same seed, a set tagged
// with := and a set tagged with :/ yield the same sequence of draws.
TEST(ConstraintDist, AssignAndDivideEquivalentForSingleValues) {
  std::vector<DistWeight> assign_set = {Single(100, 1), Single(200, 2)};
  std::vector<DistWeight> divide_set = assign_set;
  // The :/ form differs only in the per-element flag, which has no effect on a
  // single value (it governs how a range's weight is spread).
  for (auto& w : divide_set) w.per_element = true;
  auto a = SampleDist(0, 300, assign_set, 200);
  auto d = SampleDist(0, 300, divide_set, 200);
  EXPECT_EQ(a, d);
}

// 18.5.3: nonzero distribution weights do not remove values from the solution
// space. Even when one value is weighted thousands of times more heavily, the
// lightly weighted value is still reachable across many randomizations.
TEST(ConstraintDist, NonzeroWeightDoesNotExcludeValue) {
  auto vals = SampleDist(0, 100, {Single(10, 100), Single(20, 1)}, 2000);
  ASSERT_EQ(vals.size(), 2000u);
  EXPECT_GT(Count(vals, 20), 0);
}

// 18.5.3: a value whose total weight across the distribution is zero is
// excluded from the result, as though a constraint forbade it. Here 100 carries
// weight zero and is named by no other item, so only 200 is ever produced.
// (Contrast ZeroWeightItemDoesNotConstrainWhenCoveredElsewhere, where the
// zero-weighted value remains reachable through a second, nonzero item.)
TEST(ConstraintDist, ZeroTotalWeightValueExcluded) {
  auto vals = SampleDist(0, 100, {Single(100, 0), Single(200, 1)}, 200);
  ASSERT_EQ(vals.size(), 200u);
  EXPECT_EQ(Count(vals, 100), 0);
  for (int64_t v : vals) EXPECT_EQ(v, 200);
}

}  // namespace
