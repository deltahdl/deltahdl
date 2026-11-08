#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "parser/ast_expr.h"

using namespace delta;

inline Expr* ElaborateNInputGateRhs(const std::string& src, ElabFixture& f) {
  auto* design = Elaborate(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return nullptr;
  EXPECT_FALSE(f.has_errors);
  if (design->top_modules.empty()) return nullptr;
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 1u);
  if (mod->assigns.empty()) return nullptr;
  return mod->assigns.back().rhs;
}

inline std::string TwoInputGateSrc(const std::string& gate) {
  return "module m;\n  wire a, b, y;\n  " + gate + " g1(y, a, b);\nendmodule\n";
}
