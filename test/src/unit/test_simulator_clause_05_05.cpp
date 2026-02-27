
#include "preprocessor/preprocessor.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

// §5.5 Operators

// ---------------------------------------------------------------------------
// 1. Single-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorSingleCharInExpr) {
  // §5.5: Single-character operator (+) used in expression.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd10 + 8'd20;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

// ---------------------------------------------------------------------------
// 2. Double-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorDoubleCharInExpr) {
  // §5.5: Double-character operator (<<) used in expression.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd1 << 3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 8u);
}

// ---------------------------------------------------------------------------
// 3. Triple-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorTripleCharInExpr) {
  // §5.5: Triple-character operator (<<<) — arithmetic left shift.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd3 <<< 2;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

// ---------------------------------------------------------------------------
// 4. Unary operator to the left of operand
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorUnaryLeftOfOperand) {
  // §5.5: Unary operators appear to the left of their operand.
  // Unary minus (-) appears to the left of its operand.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = -8'sd5;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result & 0xFF, 251u);
}

// ---------------------------------------------------------------------------
// 5. Binary operator between operands
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorBinaryBetweenOperands) {
  // §5.5: Binary operators appear between their operands.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd50 - 8'd15;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 35u);
}

// ---------------------------------------------------------------------------
// 6. Conditional operator (two operator characters, three operands)
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorConditionalThreeOperands) {
  // §5.5: Conditional operator has two operator chars separating three
  // operands.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 1 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

// ---------------------------------------------------------------------------
// 7. Conditional operator — false branch
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorConditionalFalseBranch) {
  // §5.5: Conditional operator selects third operand when first is false.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 0 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

// ---------------------------------------------------------------------------
// 8. Multiple operator types in single expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorMixedInExpression) {
  // §5.5: Single- and double-character operators combined.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = (8'd3 + 8'd5) << 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 16u);
}

// ---------------------------------------------------------------------------
// 9. Unary negation operator
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorUnaryNegation) {
  // §5.5: Unary logical negation operator (!) to the left of operand.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = !1'b0;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

// ---------------------------------------------------------------------------
// 10. Operators without whitespace
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorNoWhitespace) {
  // §5.5: Operators work as token separators, no whitespace needed.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result=8'd7+8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}
