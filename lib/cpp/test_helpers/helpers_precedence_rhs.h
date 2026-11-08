#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"

using namespace delta;

inline Expr* ParsePrecedenceRhs(const std::string& src) {
  auto r = Parse(src);
  EXPECT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  EXPECT_NE(rhs, nullptr);
  return rhs;
}
