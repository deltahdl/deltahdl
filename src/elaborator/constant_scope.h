#pragma once

#include <string_view>

#include "elaborator/const_eval.h"

namespace delta {

struct Expr;
struct Stmt;

struct ConstantScope {
  ScopeMap fold;
  ScopeMap constants;

  void Declare(std::string_view name, const Expr* value);
};

bool DeclaresParam(const Stmt* stmt);

bool BlockDeclaresParam(const Stmt& stmt);

}  // namespace delta
