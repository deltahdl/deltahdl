// §5.5: Operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =========================================================================
// All two-char operators
// =========================================================================
TEST(ParserCh501, Sec5_1_TwoCharOperators) {
  // Exercise ==, !=, <=, >=, &&, ||, <<, >>, +=, -=, *=, /=, etc.
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial begin\n"
                      "    x = (a == b);\n"
                      "    x = (a != b);\n"
                      "    x = (a <= b);\n"
                      "    x = (a >= b);\n"
                      "    x = (a && b);\n"
                      "    x = (a || b);\n"
                      "    x = a << 1;\n"
                      "    x = a >> 1;\n"
                      "    a += 1;\n"
                      "    a -= 1;\n"
                      "    a *= 2;\n"
                      "    a /= 2;\n"
                      "  end\n"
                      "endmodule\n"));
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
TEST(ParserCh501, Sec5_1_TwoCharOperatorTokenKinds) {
  // Verify the specific TokenKind for == in an expression.
  auto r = Parse("module m;\n"
                 "  initial x = (a == b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

// =========================================================================
// All three-char operators
// =========================================================================
TEST(ParserCh501, Sec5_1_ThreeCharOperators) {
  // ===, !==, <<<, >>>, ==?, !=?
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial begin\n"
                      "    x = (a === b);\n"
                      "    x = (a !== b);\n"
                      "    x = a <<< 2;\n"
                      "    x = a >>> 2;\n"
                      "    x = (a ==? b);\n"
                      "    x = (a !=? b);\n"
                      "  end\n"
                      "endmodule\n"));
}

} // namespace
