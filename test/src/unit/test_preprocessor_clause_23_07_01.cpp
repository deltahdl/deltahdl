#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ScopeResolutionPrefixPreprocessing, ExpressionPrefixSurvives) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  initial x = Pkg::val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(ScopeResolutionPrefixPreprocessing, TypePrefixSurvives) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  Scope::my_type x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ScopeResolutionPrefixPreprocessing, ChainedPrefixSurvives) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  initial x = A::B::c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

}  // namespace
