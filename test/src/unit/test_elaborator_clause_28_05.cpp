// §28.5: buf and not gates

#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection28, ElaborateBufGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, in;\n"
      "  buf b1(out, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // buf: out = in (identity), rhs is an identifier.
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIdentifier);
}

TEST(ParserSection28, ElaborateNotGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, in;\n"
      "  not n1(out, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // not: out = ~in, rhs is unary kTilde.
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kTilde);
}

}  // namespace
