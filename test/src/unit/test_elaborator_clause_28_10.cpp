// §28.10: pullup and pulldown sources

#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection28, ElaboratePullupGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  pullup (out);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // pullup: out = 1'b1
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].rhs->int_val, 1);
}

TEST(ParserSection28, ElaboratePulldownGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  pulldown (out);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].rhs->int_val, 0);
}

}  // namespace
