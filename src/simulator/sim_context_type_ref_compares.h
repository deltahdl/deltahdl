#pragma once

#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "parser/ast_expr.h"

namespace delta {

class TypeRefCompares {
 public:
  void RecordTypeRefCompare(std::string scope, const Expr* expr, bool holds);
  void RecordUnitTypeRefCompare(const Expr* expr, bool holds);
  void SetLoweringGenBlockPrefix(std::string_view prefix);

 protected:
  std::optional<bool> TypeRefCompareIn(const Expr* expr,
                                       const std::string& scope) const;
  std::string_view LoweringGenBlockPrefix() const {
    return lowering_gen_prefix_;
  }

 private:
  std::unordered_map<const Expr*, std::unordered_map<std::string, bool>>
      type_ref_compares_;
  std::string lowering_gen_prefix_;
  std::unordered_map<const Expr*, bool> unit_type_ref_compares_;
};

}  // namespace delta
