#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexD2, AnnexDCountonesParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $countones(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexD2, AnnexDCountonesRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $countones(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD2, AnnexDIsunknownParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $isunknown(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexD2, AnnexDIsunknownRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $isunknown(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD2, AnnexDOnehot) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = $onehot(state);\n"
      "    y = $onehot0(state);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §11.2.1: $countones with constant arg is constant.
TEST(ConstExpr, CountonesConstantArg) {
  EvalFixture f;
  auto* e = ParseExprFrom("$countones(8'hFF)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

}  // namespace
