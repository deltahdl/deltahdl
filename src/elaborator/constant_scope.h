#pragma once

#include <string_view>

#include "elaborator/const_eval.h"

namespace delta {

struct Expr;
struct Stmt;

// The constants visible at a point of a design element. `fold` holds those
// whose values fold to an integer, which is what an expression written there
// folds against. `constants` holds every one of them, by name: one whose value
// folds to no integer, a real or a parameter given no default, is a constant
// all the same (§6.20), and is left out of `fold` so that nothing folds
// against a value the source never gave it. The constancy question,
// IsConstantExpr, reads names alone, so the value `constants` holds for such a
// name is never read.
struct ConstantScope {
  ScopeMap fold;
  ScopeMap constants;

  // Enters the constant `name`, declared with the value `value`, over the ones
  // entered before it, shadowing any of the same name.
  void Declare(std::string_view name, const Expr* value);
};

// Whether the statement `stmt` declares a parameter: A.2.8's
// block_item_declaration holds a parameter_declaration and a
// local_parameter_declaration, which the parser reads as a kVarDecl.
bool DeclaresParam(const Stmt* stmt);

// Whether `stmt` is a sequential or a parallel block declaring a parameter,
// whose scope (§6.20) the block bounds. A parallel block keeps its
// declarations among fork_stmts.
bool BlockDeclaresParam(const Stmt& stmt);

}  // namespace delta
