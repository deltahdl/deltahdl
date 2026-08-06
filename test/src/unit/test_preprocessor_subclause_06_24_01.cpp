#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CastOperatorParsing, IntCastThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = int'(3.14);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CastOperatorParsing, CastUnsigned) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  initial x = unsigned'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "unsigned");
}

}  // namespace
