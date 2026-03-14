#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, InsideBasicListCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 3u);
}

TEST(OperatorAndExpressionParsing, InsideBasicListLhs) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->kind, ExprKind::kIdentifier);
}

TEST(OperatorAndExpressionParsing, InsideWithRange) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[16:23], [32:47]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
}

TEST(OperatorAndExpressionParsing, InsideWithRangeElements) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[16:23], [32:47]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->elements.size(), 2u);
}

TEST(OperatorAndExpressionParsing, InsideInAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire r;\n"
      "  assign r = a inside {1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, InsideWithWildcardBits) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [2:0] val;\n"
              "  initial begin\n"
              "    while (val inside {3'b1?1}) val = val + 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, InsideWithDollarRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int a;\n"
              "  initial begin\n"
              "    if (a inside {[$:10]}) a = 0;\n"
              "  end\n"
              "endmodule\n"));
}
TEST(OperatorAndExpressionParsing, InsideMixedValuesAndRanges) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, [5:10], 20, [30:40]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 4u);
}

TEST(ExpressionParsing, InsideExprSingleValue) {
  auto r = Parse("module m; initial x = a inside {3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

TEST(ExpressionParsing, InsideExprMultipleValues) {
  auto r = Parse("module m; initial x = a inside {1, 2, 3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ExpressionParsing, InsideExprWithRange) {
  auto r = Parse("module m; initial x = a inside {[1:10]}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 1u);

  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kSelect);
}

TEST(ExpressionParsing, InsideExprMixedValuesAndRanges) {
  auto r =
      Parse("module m; initial x = a inside {5, [10:20], 30}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(OperatorAndExpressionParsing, InsideExpressionWithLhsAndElements) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (val inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(cond->elements.size(), 3u);
}

TEST(OperatorAndExpressionParsing, InsideBasicListParses) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(AggregateExpr, PackedStructInsideSet) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(AggregateExpr, PackedStructNotInSet) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 7);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
