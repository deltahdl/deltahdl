#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(IoSystemTaskParsing, StrobeSystemCall) {
  auto r = Parse(
      "module m;\n"
      "  reg a;\n"
      "  initial begin\n"
      "    $strobe(\"a=%b\", a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$strobe");
}

TEST(IoSystemTaskParsing, StrobebHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $strobeb(a);\n"
              "    $strobeh(a);\n"
              "    $strobeo(a);\n"
              "  end\n"
              "endmodule\n"));
}

// Syntax 21-2 surrounds ( list_of_arguments ) with brackets, marking the
// argument-list parenthesization as optional. The parser must therefore accept
// a bare strobe invocation with neither parentheses nor arguments.
TEST(IoSystemTaskParsing, StrobeNoArgumentListOptional) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $strobe;\n"
              "    $strobeb;\n"
              "    $strobeo;\n"
              "    $strobeh;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
