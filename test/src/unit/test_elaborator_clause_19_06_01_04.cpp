#include <gtest/gtest.h>

#include "elaborator/cross_set_expression.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// A DataType standing for the cross's CrossQueueType — the automatically
// defined queue type a cross provides (§19.6.1.3). It is the assignment target
// a cross_set_expression must evaluate to (§19.6.1.4).
DataType CrossQueueType() {
  DataType t;
  t.kind = DataTypeKind::kNamed;
  t.type_name = "CrossQueueType";
  return t;
}

// §19.6.1.4: any expression may be used to define a cross bin as long as it
// evaluates to the cross's CrossQueueType. An expression already of the cross's
// CrossQueueType is assignment compatible and may be used as written.
TEST(CrossSetExpression, MatchingCrossQueueTypeIsAllowed) {
  DataType expr = CrossQueueType();
  EXPECT_TRUE(CrossSetExpressionTypeAllowed(CrossQueueType(), expr));
}

// §19.6.1.4: a type that is assignment-incompatible with the cross type cannot
// be used as written. A string expression does not evaluate to the cross's
// CrossQueueType and is rejected.
TEST(CrossSetExpression, IncompatibleTypeIsNotAllowed) {
  DataType expr;
  expr.kind = DataTypeKind::kString;
  EXPECT_FALSE(CrossSetExpressionTypeAllowed(CrossQueueType(), expr));
}

// §19.6.1.4: no cast is required when the expression's type is assignment
// compatible with the cross's CrossQueueType.
TEST(CrossSetExpression, CompatibleTypeRequiresNoCast) {
  DataType expr = CrossQueueType();
  EXPECT_FALSE(CrossSetExpressionCastRequired(CrossQueueType(), expr));
}

// §19.6.1.4: a cast is required when the expression's type is
// assignment-incompatible with the cross type.
TEST(CrossSetExpression, IncompatibleTypeRequiresCast) {
  DataType expr;
  expr.kind = DataTypeKind::kString;
  EXPECT_TRUE(CrossSetExpressionCastRequired(CrossQueueType(), expr));
}

// §19.6.1.4: the cross supplies a specific context type, so an expression of a
// different named type — not the cross's CrossQueueType — is assignment
// incompatible and cannot be used as written. This exercises discrimination by
// named-type identity, the realistic incompatibility for a cross_set_expression
// whose target is itself a named aggregate type.
TEST(CrossSetExpression, DifferentNamedTypeIsNotAllowed) {
  DataType expr;
  expr.kind = DataTypeKind::kNamed;
  expr.type_name = "SomeOtherQueueType";
  EXPECT_FALSE(CrossSetExpressionTypeAllowed(CrossQueueType(), expr));
}

// §19.6.1.4: a cast is required when the expression is a different named type
// than the cross's CrossQueueType, since that is assignment-incompatible with
// the cross type.
TEST(CrossSetExpression, DifferentNamedTypeRequiresCast) {
  DataType expr;
  expr.kind = DataTypeKind::kNamed;
  expr.type_name = "SomeOtherQueueType";
  EXPECT_TRUE(CrossSetExpressionCastRequired(CrossQueueType(), expr));
}

// §19.6.1.4: the allowed/cast-required decisions are exact complements — an
// expression is usable as written exactly when no cast is required, for both a
// compatible and an incompatible expression type.
TEST(CrossSetExpression, AllowedAndCastRequiredAreComplementary) {
  DataType compatible = CrossQueueType();
  DataType incompatible;
  incompatible.kind = DataTypeKind::kString;

  EXPECT_NE(CrossSetExpressionTypeAllowed(CrossQueueType(), compatible),
            CrossSetExpressionCastRequired(CrossQueueType(), compatible));
  EXPECT_NE(CrossSetExpressionTypeAllowed(CrossQueueType(), incompatible),
            CrossSetExpressionCastRequired(CrossQueueType(), incompatible));
}

}  // namespace
