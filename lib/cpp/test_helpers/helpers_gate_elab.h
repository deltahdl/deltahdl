#pragma once

#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

// Elaborates a single-instance module whose body is the given primitive
// instantiation (e.g. "bufif1 b1(y, a, en);") wired against the standard
// "wire y, a, en;" net declaration, runs the assertions common to every
// gate/switch lowering test, and returns the module's first continuous
// assignment. Returns nullptr (after firing a gtest failure) if elaboration
// did not produce the expected structure, so callers can guard with
// ASSERT_NE before dereferencing.
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

// Elaborates the given primitive instantiation and returns the right-hand side
// expression of the module's first continuous assignment (the lowered drive
// expression). Returns nullptr (after firing a gtest failure) on any
// structural mismatch.
//
// A MOS switch's drive tests its data for z ahead of the conditional its
// control selects with (§28.7 Table 28-6 gives z data a z output whatever the
// control), so for one the conditional answered is the one behind that test.
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

// Asserts that the lowered drive expression is a conditional whose enabling
// condition is "en", that conducts data "a" when enabled and drives Z when
// blocked (e.g. bufif1, nmos). Verifies the explicit condition terminal.
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

// Asserts that the lowered drive expression is a conditional that drives Z on
// its true arm and conducts data "a" on its false arm (e.g. bufif0, pmos,
// rpmos: conduct on inactive/zero control without inverting).
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

// Asserts that the lowered drive expression is a conditional that conducts data
// "a" on its true arm (non-inverting) and drives Z on its false arm, without
// checking the condition terminal (e.g. rnmos).
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
