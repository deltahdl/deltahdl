#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DottedNamePreprocessing, DottedNameSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  typedef struct { int x; } s_t;\n"
      "  s_t s;\n"
      "  initial s.x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(DottedNamePreprocessing, MultiLevelDottedNameSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  typedef struct { int x; } inner_t;\n"
      "  typedef struct { inner_t sub; } outer_t;\n"
      "  outer_t o;\n"
      "  initial o.sub.x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

}  // namespace
