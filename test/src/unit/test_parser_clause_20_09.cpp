#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskExtendedParsing, CountonesParse) {
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

TEST(OptionalSystemTaskExtendedParsing, CountonesRhs) {
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

TEST(OptionalSystemTaskExtendedParsing, IsunknownParse) {
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

TEST(OptionalSystemTaskExtendedParsing, IsunknownRhs) {
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

TEST(OptionalSystemTaskExtendedParsing, Onehot) {
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

}  // namespace
