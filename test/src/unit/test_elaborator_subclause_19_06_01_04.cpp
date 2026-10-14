#include <gtest/gtest.h>

#include "elaborator/cross_set_expression.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

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

// §19.6.1.4: a cross_set_expression has the cross's CrossQueueType, a queue
// of structures, so a queue of int, string or real elements is an error and a
// queue of structures is not.
TEST(CrossSetExpression, QueueOfIntegralRealOrStringElementsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  string s[$] = '{\"x\"};\n"
      "  real r[$];\n"
      "  typedef struct {bit [1:0] a; bit [1:0] b;} pair_t;\n"
      "  pair_t ok[$];\n"
      "  covergroup cg;\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    X: cross a, b {\n"
      "      bins one = q;\n"
      "      bins two = s;\n"
      "      bins three = r;\n"
      "      bins four = ok;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the cross_set_expression 'q' of bin 'one' is no "
                            "queue of the cross's CrossValType",
                            12, "19.6.1.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the cross_set_expression 's' of bin 'two' is no "
                            "queue of the cross's CrossValType",
                            13, "19.6.1.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the cross_set_expression 'r' of bin 'three' is no "
                            "queue of the cross's CrossValType",
                            14, "19.6.1.4"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
