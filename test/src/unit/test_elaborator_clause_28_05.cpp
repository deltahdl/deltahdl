#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(BufNotElaboration, ElaborateNotGate) {
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

  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kTilde);
}

// The last terminal connects to the input. buf lowers to a double complement
// (Table 28-4 normalizes a z input to x), so the driven operand is reached by
// stripping the two inversions.
TEST(BufNotElaboration, LastTerminalIsInput) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, in;\n"
      "  buf b1(out, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].lhs->text, "out");
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  ASSERT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->lhs->text, "in");
}

TEST(BufNotElaboration, MultiOutputBufEmitsOneAssignPerOutput) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire o1, o2, in;\n"
      "  buf b1(o1, o2, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->assigns[0].lhs->text, "o1");
  EXPECT_EQ(mod->assigns[1].lhs->text, "o2");
  // Each output is driven by the shared input, normalized through the buf
  // double complement (Table 28-4).
  for (auto& ca : mod->assigns) {
    ASSERT_NE(ca.rhs, nullptr);
    ASSERT_EQ(ca.rhs->kind, ExprKind::kUnary);
    EXPECT_EQ(ca.rhs->op, TokenKind::kTilde);
    ASSERT_NE(ca.rhs->lhs, nullptr);
    ASSERT_EQ(ca.rhs->lhs->kind, ExprKind::kUnary);
    EXPECT_EQ(ca.rhs->lhs->op, TokenKind::kTilde);
    ASSERT_NE(ca.rhs->lhs->lhs, nullptr);
    EXPECT_EQ(ca.rhs->lhs->lhs->kind, ExprKind::kIdentifier);
    EXPECT_EQ(ca.rhs->lhs->lhs->text, "in");
  }
}

TEST(BufNotElaboration, MultiOutputNotEmitsInvertedAssignsPerOutput) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire o1, o2, in;\n"
      "  not n1(o1, o2, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  for (auto& ca : mod->assigns) {
    ASSERT_NE(ca.rhs, nullptr);
    EXPECT_EQ(ca.rhs->kind, ExprKind::kUnary);
    EXPECT_EQ(ca.rhs->op, TokenKind::kTilde);
    ASSERT_NE(ca.rhs->lhs, nullptr);
    EXPECT_EQ(ca.rhs->lhs->text, "in");
  }
}

}  // namespace
