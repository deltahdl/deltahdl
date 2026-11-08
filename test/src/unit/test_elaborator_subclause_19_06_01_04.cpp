#include <gtest/gtest.h>

#include "elaborator/cross_set_expression.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

DataType CrossQueueType() {
  DataType t;
  t.kind = DataTypeKind::kNamed;
  t.type_name = "CrossQueueType";
  return t;
}

TEST(CrossSetExpression, MatchingCrossQueueTypeIsAllowed) {
  DataType expr = CrossQueueType();
  EXPECT_TRUE(CrossSetExpressionTypeAllowed(CrossQueueType(), expr));
}

TEST(CrossSetExpression, IncompatibleTypeIsNotAllowed) {
  DataType expr;
  expr.kind = DataTypeKind::kString;
  EXPECT_FALSE(CrossSetExpressionTypeAllowed(CrossQueueType(), expr));
}

TEST(CrossSetExpression, CompatibleTypeRequiresNoCast) {
  DataType expr = CrossQueueType();
  EXPECT_FALSE(CrossSetExpressionCastRequired(CrossQueueType(), expr));
}

TEST(CrossSetExpression, IncompatibleTypeRequiresCast) {
  DataType expr;
  expr.kind = DataTypeKind::kString;
  EXPECT_TRUE(CrossSetExpressionCastRequired(CrossQueueType(), expr));
}

TEST(CrossSetExpression, DifferentNamedTypeIsNotAllowed) {
  DataType expr;
  expr.kind = DataTypeKind::kNamed;
  expr.type_name = "SomeOtherQueueType";
  EXPECT_FALSE(CrossSetExpressionTypeAllowed(CrossQueueType(), expr));
}

TEST(CrossSetExpression, DifferentNamedTypeRequiresCast) {
  DataType expr;
  expr.kind = DataTypeKind::kNamed;
  expr.type_name = "SomeOtherQueueType";
  EXPECT_TRUE(CrossSetExpressionCastRequired(CrossQueueType(), expr));
}

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
