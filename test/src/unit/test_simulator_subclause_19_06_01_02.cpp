#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// In the with_covergroup_expression, the cross_items stand for the values each
// coverpoint takes in a value tuple. CountSatisfyingValueTuples enumerates the
// Cartesian product of a candidate bin tuple's value sets and reports how many
// of those value tuples satisfy the predicate (LRM 19.6.1.2).
TEST(CrossWithCovergroup, CountsSatisfyingValueTuplesOverCartesianProduct) {
  // Bin tuple <{0,1,2}, {10,20}> has 3 x 2 = 6 value tuples.
  std::vector<std::vector<int64_t>> sets = {{0, 1, 2}, {10, 20}};
  // a + b < 21 : <0,10> <0,20> <1,10> <2,10> satisfy; <1,20> <2,20> do not.
  auto pred = [](const std::vector<int64_t>& t) { return t[0] + t[1] < 21; };

  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples(sets, pred), 4u);
}

// A coverpoint with an empty value set (or no coverpoints at all) yields no
// value tuples, so nothing can satisfy the expression (LRM 19.6.1.2).
TEST(CrossWithCovergroup, NoValueTuplesWhenAnySetIsEmpty) {
  auto any = [](const std::vector<int64_t>&) { return true; };
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples({{1, 2}, {}}, any), 0u);
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples({}, any), 0u);
}

// A bare cross_identifier select_expression (no with clause) selects every
// candidate bin tuple of the enclosing cross (LRM 19.6.1.2).
TEST(CrossWithCovergroup, BareCrossIdentifierSelectsAllBinTuples) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {
      {{0}, {0}}, {{0}, {1}}, {{1}, {0}}, {{1}, {1}}};
  CrossWithMatchPolicy policy;  // unused without a predicate

  auto selected =
      CoverageDB::SelectCrossBinTuples(candidates, /*pred=*/nullptr, policy);
  EXPECT_EQ(selected, (std::vector<size_t>{0, 1, 2, 3}));
}

// With a with clause and no matches clause, the selection policy defaults to
// one: a candidate is kept when at least one value tuple satisfies the
// expression (LRM 19.6.1.2).
TEST(CrossWithCovergroup, WithClauseDefaultsToAtLeastOne) {
  // candidate 0: <{0},{0}> sum 0; candidate 1: <{5},{5}> sum 10.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0}, {0}},
                                                               {{5}, {5}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>& t) { return t[0] + t[1] < 1; };
  CrossWithMatchPolicy policy;  // default: require_all false, min_count 1

  auto selected = CoverageDB::SelectCrossBinTuples(candidates, &pred, policy);
  EXPECT_EQ(selected, (std::vector<size_t>{0}));  // only candidate 0 satisfies
}

// A matches clause with a positive integer N keeps a candidate only when at
// least N of its value tuples satisfy the expression (LRM 19.6.1.2).
TEST(CrossWithCovergroup, MatchesIntegerRequiresMinimumCount) {
  // candidate 0: <{0,1},{0}>     -> tuples <0,0>,<1,0>, 2 satisfy a+b<2.
  // candidate 1: <{0,5},{0}>     -> tuples <0,0>,<5,0>, 1 satisfies a+b<2.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>& t) { return t[0] + t[1] < 2; };

  CrossWithMatchPolicy two;
  two.min_count = 2;
  EXPECT_EQ(CoverageDB::SelectCrossBinTuples(candidates, &pred, two),
            (std::vector<size_t>{0}));

  CrossWithMatchPolicy one;  // min_count 1
  EXPECT_EQ(CoverageDB::SelectCrossBinTuples(candidates, &pred, one),
            (std::vector<size_t>{0, 1}));
}

// The $ matches form requires every value tuple of the candidate to satisfy the
// expression for the candidate to be selected (LRM 19.6.1.2).
TEST(CrossWithCovergroup, MatchesDollarRequiresAllValueTuples) {
  // candidate 0: <{0,1},{0}> -> all of <0,0>,<1,0> satisfy a+b<2.
  // candidate 1: <{0,5},{0}> -> <5,0> fails a+b<2, so not all satisfy.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>& t) { return t[0] + t[1] < 2; };

  CrossWithMatchPolicy all;
  all.require_all = true;
  EXPECT_EQ(CoverageDB::SelectCrossBinTuples(candidates, &pred, all),
            (std::vector<size_t>{0}));
}

// Each cross_item maps to its own coverpoint's value within a value tuple:
// position i of the tuple is the value of the i-th coverpoint of the cross. A
// predicate that pins each position observes the ordering (LRM 19.6.1.2).
TEST(CrossWithCovergroup, ValueTupleMapsEachCrossItemToItsCoverpoint) {
  // Three single-value coverpoints yield exactly one value tuple, <2,3,4>.
  std::vector<std::vector<int64_t>> sets = {{2}, {3}, {4}};

  auto ordered = [](const std::vector<int64_t>& t) {
    return t[0] == 2 && t[1] == 3 && t[2] == 4;
  };
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples(sets, ordered), 1u);

  // Expecting the values in reversed coverpoint order matches no value tuple.
  auto reversed = [](const std::vector<int64_t>& t) {
    return t[0] == 4 && t[1] == 3 && t[2] == 2;
  };
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples(sets, reversed), 0u);
}

// A matches count greater than the candidate's total number of value tuples can
// never be met, so the candidate is not selected even when every value tuple
// satisfies the expression (LRM 19.6.1.2).
TEST(CrossWithCovergroup, MatchesCountAboveTupleCountSelectsNothing) {
  // One candidate with 2 value tuples, both satisfying the predicate.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>&) { return true; };

  CrossWithMatchPolicy three;
  three.min_count = 3;  // exceeds the 2 available value tuples
  EXPECT_TRUE(
      CoverageDB::SelectCrossBinTuples(candidates, &pred, three).empty());
}

// The $ form selects a candidate only when it has value tuples and all satisfy:
// a candidate with an empty value set has no value tuples, so it is not
// selected (LRM 19.6.1.2).
TEST(CrossWithCovergroup, MatchesDollarRejectsCandidateWithNoValueTuples) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{1, 2}, {}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>&) { return true; };

  CrossWithMatchPolicy all;
  all.require_all = true;
  EXPECT_TRUE(CoverageDB::SelectCrossBinTuples(candidates, &pred, all).empty());
}

}  // namespace
