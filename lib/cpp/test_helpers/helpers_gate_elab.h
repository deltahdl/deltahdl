#pragma once

#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

inline const RtlirContAssign* ElaborateSingleGateAssign(
    const std::string& instantiation, ElabFixture& f) {
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  " +
          instantiation + "\n" + "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return nullptr;
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 1u);
  if (mod->assigns.empty()) return nullptr;
  return &mod->assigns[0];
}

inline const Expr* ElaborateSingleGateRhs(const std::string& instantiation,
                                          ElabFixture& f) {
  const auto* assign = ElaborateSingleGateAssign(instantiation, f);
  EXPECT_NE(assign, nullptr);
  if (assign == nullptr) return nullptr;
  EXPECT_NE(assign->rhs, nullptr);
  const Expr* rhs = assign->rhs;
  if (rhs != nullptr && rhs->kind == ExprKind::kTernary &&
      rhs->condition != nullptr && rhs->condition->op == TokenKind::kEqEqEq) {
    return rhs->false_expr;
  }
  return rhs;
}

inline void ExpectConductsAOnEnableElseZ(const std::string& instantiation,
                                         ElabFixture& f) {
  const auto* rhs = ElaborateSingleGateRhs(instantiation, f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->text, "en");
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->true_expr->text, "a");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
}

inline void ExpectZOnTrueArmConductsAOnFalseArm(
    const std::string& instantiation, ElabFixture& f) {
  const auto* rhs = ElaborateSingleGateRhs(instantiation, f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->false_expr->text, "a");
}

inline void ExpectConductsAOnTrueArmZOnFalseArm(
    const std::string& instantiation, ElabFixture& f) {
  const auto* rhs = ElaborateSingleGateRhs(instantiation, f);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->true_expr->text, "a");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
}
