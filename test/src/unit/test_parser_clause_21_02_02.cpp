// §21.2.2: Strobed monitoring

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// ---------------------------------------------------------------------------
// 10. $strobe system call (Postponed region sampling)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_StrobeSystemCall) {
  auto r = Parse("module m;\n"
                 "  reg a;\n"
                 "  initial begin\n"
                 "    $strobe(\"a=%b\", a);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$strobe");
}

TEST(ParserSection21, StrobeBasicCall) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  initial $strobe(\"val=%d\", x);\n"
                      "endmodule\n"));
}

TEST(ParserSection21, StrobebHexOctal) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  initial begin\n"
                      "    $strobeb(a);\n"
                      "    $strobeh(a);\n"
                      "    $strobeo(a);\n"
                      "  end\n"
                      "endmodule\n"));
}

} // namespace
