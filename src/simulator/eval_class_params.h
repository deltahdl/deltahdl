#pragma once

#include <cstddef>
#include <string_view>

#include "common/types.h"
#include "elaborator/const_eval.h"

namespace delta {

class Arena;
struct ClassDecl;
struct DataType;
struct Expr;
class SimContext;

// §8.25 (printed page 203) with §6.20.2 (printed 126-127) and §11.6.1: a
// class's value parameters, each sized by the type its declaration writes.
// A default or a specialization's actual is the right-hand side of an
// assignment to the parameter, so it is evaluated at the declared width --
// an unbased unsized literal filling `logic [W-1:0]` (§5.7.1), a wider actual
// cut to it -- and §8.25.1 lets the range name an earlier parameter, so the
// parameters are taken in header order and each one's value is recorded for
// the ranges after it. A type that fixes no width, one whose bounds do not
// fold, a real and a typedef name leave the value self-determined, as every
// parameter was before.
class ClassParamSizer {
 public:
  explicit ClassParamSizer(const ClassDecl* decl) : decl_(decl) {}

  // The value of the class's i-th parameter from `expr`, and recorded.
  Logic4Vec Value(size_t i, const Expr* expr, SimContext& ctx, Arena& arena);

  // The value of a parameter declared with `type` -- a body parameter's, which
  // the header's list does not index -- from `expr`, recorded under `name`.
  Logic4Vec Value(std::string_view name, const DataType* type, const Expr* expr,
                  SimContext& ctx, Arena& arena);

  // Records the i-th parameter's value that stands already, for the ranges
  // after it: an object's default kept beside a specialization's overrides.
  void Record(size_t i, const Logic4Vec& val);

 private:
  const ClassDecl* decl_;
  ScopeMap scope_;
};

}  // namespace delta
