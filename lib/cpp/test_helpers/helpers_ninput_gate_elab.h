#pragma once

#include <string>

#include "fixture_elaborator.h"

using namespace delta;

// Elaborates a single n-input gate module and returns the RHS expression of the
// last continuous assign the elaborator emits. Performs the "design elaborated
// without errors and produced at least one assign" checks that every n-input
// gate elaboration test repeats. Returns nullptr (after firing a gtest failure)
// on a structural mismatch so callers can ASSERT_NE before dereferencing.
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

// Source for a single two-input gate `g1(y, a, b)` of the given primitive
// (e.g. "or", "nand", "nor", "xnor"), with the standard "wire a, b, y;" layout.
inline std::string TwoInputGateSrc(const std::string& gate) {
  return "module m;\n  wire a, b, y;\n  " + gate + " g1(y, a, b);\nendmodule\n";
}
