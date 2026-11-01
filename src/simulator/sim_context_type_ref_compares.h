#pragma once

#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "parser/ast_expr.h"

namespace delta {

// §6.23 with §6.20.3: a comparison of two type references holds exactly when
// the two types match in the scope it is written in, and every instance of a
// module, and every generate block instance within it, is a scope of its own
// while they all share the one tree. The elaborator judges each comparison
// once per scope and the lowerer records the answers here, keyed by the
// instance's prefix followed by the generate block instance's. A base class of
// SimContext, which keeps the lookup that needs its running process
// (SimContext::TypeRefCompareHere). Defined in sim_context_scope.cpp.
class TypeRefCompares {
 public:
  void RecordTypeRefCompare(std::string scope, const Expr* expr, bool holds);
  // §27.4: the generate block instance declaring what is being built, where
  // that is a declaration whose initializer is evaluated before any process.
  void SetLoweringGenBlockPrefix(std::string_view prefix);

 protected:
  // The answer recorded for `expr` in `scope`, or nullopt where none is.
  std::optional<bool> TypeRefCompareIn(const Expr* expr,
                                       const std::string& scope) const;
  std::string_view LoweringGenBlockPrefix() const {
    return lowering_gen_prefix_;
  }

 private:
  std::unordered_map<const Expr*, std::unordered_map<std::string, bool>>
      type_ref_compares_;
  std::string lowering_gen_prefix_;
};

}  // namespace delta
