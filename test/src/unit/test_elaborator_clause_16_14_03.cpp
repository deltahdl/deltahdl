#include <gtest/gtest.h>

#include "elaborator/cover_pass_statement.h"

using namespace delta;

namespace {

// §16.14.3: a cover statement's pass statement shall not include any concurrent
// assert, assume, or cover statement.
TEST(CoverPassStatement, RejectsConcurrentAssertionStatements) {
  EXPECT_FALSE(
      CoverPassStatementAllows(CoverPassStatementForm::kConcurrentAssert));
  EXPECT_FALSE(
      CoverPassStatementAllows(CoverPassStatementForm::kConcurrentAssume));
  EXPECT_FALSE(
      CoverPassStatementAllows(CoverPassStatementForm::kConcurrentCover));
}

// §16.14.3: an ordinary statement (e.g. a $display or assignment) is permitted
// as the optional pass statement.
TEST(CoverPassStatement, AllowsOrdinaryStatements) {
  EXPECT_TRUE(CoverPassStatementAllows(CoverPassStatementForm::kOther));
}

}  // namespace
