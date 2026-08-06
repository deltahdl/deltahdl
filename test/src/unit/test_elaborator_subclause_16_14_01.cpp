#include <gtest/gtest.h>

#include "elaborator/concurrent_assert_action.h"

using namespace delta;

namespace {

// §16.14.1: an assert statement's action_block shall not include any concurrent
// assert, assume, or cover statement.
TEST(AssertActionBlock, RejectsConcurrentAssertionStatements) {
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssert));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssume));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentCover));
}

// §16.14.1: the action_block may contain immediate assertion statements.
TEST(AssertActionBlock, AllowsImmediateAssertions) {
  EXPECT_TRUE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kImmediateAssertion));
}

// §16.14.1: ordinary statements (e.g. a $display or assignment) are permitted.
TEST(AssertActionBlock, AllowsOrdinaryStatements) {
  EXPECT_TRUE(
      ConcurrentAssertActionBlockAllows(ActionBlockStatementForm::kOther));
}

}  // namespace
