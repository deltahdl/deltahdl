#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// §19.5.1.2: the set_covergroup_expression is evaluated when the covergroup
// instance is constructed, so it is evaluated exactly once.
TEST(CoverageSetExpression, EvaluatedOnceAtConstruction) {
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(0), 1u);
}

// §19.5.1.2: evaluation happens at construction, not at each sampling point, so
// the count stays one no matter how many times the instance is sampled.
TEST(CoverageSetExpression, NotReevaluatedPerSample) {
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(1), 1u);
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(100), 1u);
}

}  // namespace
