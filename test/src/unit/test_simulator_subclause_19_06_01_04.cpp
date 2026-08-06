#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// §19.6.1.4: a cross_set_expression yields a queue of value tuples (the cross's
// CrossQueueType, elements of type CrossValType — one component per coverpoint,
// §19.6.1.3). A bin tuple is selected by the number of its value tuples that
// are present as elements of that queue, under the same matches policy as the
// with covergroup expression (§19.6.1.2). This mirrors the LRM example
//   aXb : cross a, b { bins one = '{ '{1,2}, '{3,4}, '{5,6} }; }
// whose queue selects the bin tuples <a.x[1],b.y[2]>, <a.x[3],b.y[4]>, and
// <a.x[5],b.y[6]> — the candidates whose single value tuple appears in the
// queue — under the default policy of one.
TEST(CrossSetExpressionSelect, ArrayLiteralQueueSelectsMatchingBinTuples) {
  // The queue from the LRM example: three value tuples.
  std::vector<std::vector<int64_t>> queue = {{1, 2}, {3, 4}, {5, 6}};
  // Single-value candidate bin tuples <1,2>, <3,4>, <5,6> are present; the
  // interleaving candidate <1,4> is not in the queue.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {
      {{1}, {2}}, {{1}, {4}}, {{3}, {4}}, {{5}, {6}}};
  CrossWithMatchPolicy policy;  // default: require_all false, min_count 1

  auto selected = CoverageDB::SelectCrossBinTuplesBySetExpression(
      candidates, queue, policy);
  EXPECT_EQ(selected, (std::vector<size_t>{0, 2, 3}));
}

// §19.6.1.4: the default policy is one — a single value tuple of the bin tuple
// present in the cross_set_expression selects it. A candidate spanning several
// value tuples is kept as soon as any one of them is a queue element.
TEST(CrossSetExpressionSelect, DefaultPolicySelectsOnAnyPresentValueTuple) {
  std::vector<std::vector<int64_t>> queue = {{2, 7}};
  // Candidate <{1,2},{7}> enumerates value tuples <1,7> and <2,7>; only <2,7>
  // is present, but one presence suffices under the default policy.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{1, 2}, {7}}};
  CrossWithMatchPolicy policy;

  EXPECT_EQ(CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue,
                                                            policy),
            (std::vector<size_t>{0}));
}

// §19.6.1.4 (negative): a bin tuple whose value tuples are all absent from the
// cross_set_expression queue is not selected — the closest rejecting input to
// the accepting path above.
TEST(CrossSetExpressionSelect, BinTupleAbsentFromQueueIsNotSelected) {
  std::vector<std::vector<int64_t>> queue = {{1, 2}, {3, 4}};
  // Candidate <9,9> — neither of its (single) value tuples is in the queue.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{9}, {9}}};
  CrossWithMatchPolicy policy;

  EXPECT_TRUE(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, policy)
          .empty());
}

// §19.6.1.4: the optional matches expression sets how many value tuples of a
// bin tuple shall be present in the cross_set_expression for the tuple to be
// selected. With matches N, a candidate is kept only when at least N of its
// value tuples are queue elements.
TEST(CrossSetExpressionSelect, MatchesIntegerRequiresMinimumPresentCount) {
  std::vector<std::vector<int64_t>> queue = {{0, 0}, {1, 0}};
  // candidate 0: <{0,1},{0}> -> value tuples <0,0>,<1,0>, both present.
  // candidate 1: <{0,5},{0}> -> value tuples <0,0>,<5,0>, only <0,0> present.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};

  CrossWithMatchPolicy two;
  two.min_count = 2;
  EXPECT_EQ(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, two),
      (std::vector<size_t>{0}));

  CrossWithMatchPolicy one;  // min_count 1 (the default policy)
  EXPECT_EQ(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, one),
      (std::vector<size_t>{0, 1}));
}

// §19.6.1.4: the $ matches form requires every value tuple of the candidate bin
// tuple to be present in the cross_set_expression for the candidate to be
// selected, the same require_all policy the with covergroup expression uses.
TEST(CrossSetExpressionSelect, MatchesDollarRequiresAllValueTuplesPresent) {
  std::vector<std::vector<int64_t>> queue = {{0, 0}, {1, 0}};
  // candidate 0: <{0,1},{0}> -> both <0,0>,<1,0> present.
  // candidate 1: <{0,5},{0}> -> <5,0> is absent, so not all present.
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};

  CrossWithMatchPolicy all;
  all.require_all = true;
  EXPECT_EQ(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, all),
      (std::vector<size_t>{0}));
}

// §19.6.1.4: an empty cross_set_expression queue holds no value tuples, so no
// candidate bin tuple has a value tuple present in it and none is selected.
TEST(CrossSetExpressionSelect, EmptyQueueSelectsNothing) {
  std::vector<std::vector<int64_t>> queue;  // empty cross_set_expression
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{1}, {2}},
                                                               {{3}, {4}}};
  CrossWithMatchPolicy policy;

  EXPECT_TRUE(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, policy)
          .empty());
}

}  // namespace
