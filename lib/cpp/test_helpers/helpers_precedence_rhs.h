#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

// Parse a module whose first initial block assigns an expression, then return
// that assignment's RHS after asserting a clean parse. Used by the operator
// precedence/associativity tests, which all share this parse-and-fetch setup
// and differ only in the source text and the per-test operator assertions.
inline Expr* ParsePrecedenceRhs(const std::string& src) {
  auto r = Parse(src);
  EXPECT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  EXPECT_NE(rhs, nullptr);
  return rhs;
}
