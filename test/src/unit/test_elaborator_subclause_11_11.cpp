#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

int64_t FoldedTripleParam(ElabFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = (11:22:33);\n"
      "endmodule\n",
      f);
  if (design == nullptr) {
    ADD_FAILURE() << "the source did not elaborate, so nothing folded";
    return 0;
  }
  EXPECT_FALSE(f.has_errors);
  const auto* p = FindParam(design, "m", "P");
  if (p == nullptr) {
    ADD_FAILURE() << "the elaborated design declares no parameter P";
    return 0;
  }
  return p->resolved_value;
}

TEST(MinTypMaxElaboration, TypicalMemberFoldsWhenNoDelayModeGuardIsLive) {
  ElabFixture f;
  EXPECT_EQ(FoldedTripleParam(f), 22);
}

TEST(MinTypMaxElaboration, MinimumMemberFoldsWhileAMinimumGuardIsLive) {
  ElabFixture f;
  DelayModeGuard guard(DelayMode::kMin);
  EXPECT_EQ(FoldedTripleParam(f), 11);
}

TEST(MinTypMaxElaboration, MaximumMemberFoldsWhileAMaximumGuardIsLive) {
  ElabFixture f;
  DelayModeGuard guard(DelayMode::kMax);
  EXPECT_EQ(FoldedTripleParam(f), 33);
}

TEST(MinTypMaxElaboration, AGuardRestoresTheModeItFoundRatherThanTheDefault) {
  DelayModeGuard outer(DelayMode::kMax);
  {
    ElabFixture under_inner;
    DelayModeGuard inner(DelayMode::kMin);
    EXPECT_EQ(FoldedTripleParam(under_inner), 11);
  }
  EXPECT_EQ(ActiveDelayMode(), DelayMode::kMax);
  ElabFixture after_inner;
  EXPECT_EQ(FoldedTripleParam(after_inner), 33);
}

constexpr std::string_view kSizedTriple = "(4'd1:8'd2:16'd3)";

TEST(MinTypMaxElaboration, WidthIsTheTypicalMembersByDefault) {
  EvalFixture f;
  auto* e = ParseExprFrom(std::string(kSizedTriple), f);
  ASSERT_NE(e, nullptr);
  ASSERT_EQ(e->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(InferExprWidth(e, {}), 8u);
}

TEST(MinTypMaxElaboration, WidthFollowsTheSelectedMember) {
  EvalFixture f;
  auto* e = ParseExprFrom(std::string(kSizedTriple), f);
  ASSERT_NE(e, nullptr);
  DelayModeGuard guard(DelayMode::kMin);
  EXPECT_EQ(InferExprWidth(e, {}), 4u);
}

TEST(MinTypMaxElaboration, WidthTakesNeitherTheWidestNorTheNarrowest) {
  EvalFixture f;
  auto* e = ParseExprFrom(std::string(kSizedTriple), f);
  ASSERT_NE(e, nullptr);
  DelayModeGuard guard(DelayMode::kMax);
  EXPECT_EQ(InferExprWidth(e, {}), 16u);
}

TEST(TypeReferenceOperatorElaboration, UnaryAndConditionalOnTypeRefReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic r, c;\n"
      "  initial r = !type(int);\n"
      "  initial r = c ? type(int) : 1'b0;\n"
      "  initial r = c ? 1'b0 : type(byte);\n"
      "  initial r = type(int) ? 1'b1 : 1'b0;\n"
      "  initial r = !c ? 1'b1 : 1'b0;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a type reference may only be used with the "
                              "equality, inequality, and case "
                              "equality/inequality operators",
                              line, "6.23"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "a type reference may only be used", 7, "6.23"));
}

}  // namespace
