#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Integration robustness: a ::-prefixed name passes through the preprocessor
// intact so the elaborator can apply the §23.7.1 resolution rules to it.
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

}  // namespace
