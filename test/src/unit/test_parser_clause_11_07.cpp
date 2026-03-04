// §11.7: Signed expressions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// Section 11.7 -- Signed expressions ($signed, $unsigned)
// =========================================================================
TEST(ParserSection11, SignedSystemCall) {
  auto r = Parse("module t;\n"
                 "  initial x = $signed(a);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$signed");
}

TEST(ParserSection11, UnsignedSystemCall) {
  auto r = Parse("module t;\n"
                 "  initial x = $unsigned(a);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$unsigned");
}

} // namespace
