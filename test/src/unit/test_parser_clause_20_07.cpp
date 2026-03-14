#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AggregateTypeParsing, ArrayDimensionsQuery) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4][8];\n"
      "  initial x = $dimensions(arr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$dimensions");
}

TEST(AggregateTypeParsing, ArraySizeQuery) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = $size(arr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$size");
}

TEST(UtilitySystemTaskParsing, ArrayLeftFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $left(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UtilitySystemTaskParsing, ArrayRightFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $right(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UtilitySystemTaskParsing, ArraySizeFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr [16];\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $size(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UtilitySystemTaskParsing, ArrayHighLowFunctions) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] mem [0:255];\n"
      "  initial begin\n"
      "    $display(\"high=%0d low=%0d\", $high(mem), $low(mem));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UtilitySystemTaskParsing, ArrayDimensionsFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0][7:0] data;\n"
      "  initial begin\n"
      "    int d;\n"
      "    d = $dimensions(data);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UtilitySystemTaskParsing, ArrayIncrementFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $increment(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UtilitySystemTaskParsing, ArraySizeWithDimArg) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:15];\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $size(mem, 2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UtilitySystemTaskParsing, ArrayUnpackedDimensionsFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic arr [4][8];\n"
      "  initial begin\n"
      "    int d;\n"
      "    d = $unpacked_dimensions(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
