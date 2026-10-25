// The index keys of an array assignment pattern, `'{ array_pattern_key :
// expression { , array_pattern_key : expression } }` (A.6.7.1), wherever
// ArrayPatternCheck reaches one: each is a constant expression, and each names
// its element once.

#include <format>
#include <optional>
#include <string>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_key_match.h"
#include "parser/ast_expr.h"

namespace delta {

std::optional<std::string> ArrayPatternKeyIdentity(const Expr* key) {
  auto value = ConstEvalInt(key);
  if (value) return std::to_string(*value);
  if (key->text.empty()) return std::nullopt;
  return std::string(key->text);
}

void CheckArrayPatternIndexKeys(const ArrayPatternCheck& check,
                                const Expr* pattern, SourceLoc loc) {
  std::unordered_set<std::string> seen;
  for (const auto* key : pattern->pattern_keys) {
    if (key->text == "default" || IsTypeKey(key->text, check.typedefs)) {
      continue;
    }
    if (NamesAVariable(key, check.var_types)) {
      check.diag.Error(key->range.start,
                       "an array pattern's index key is a constant "
                       "expression, which names no variable",
                       Subclause("A.6.7.1"));
      continue;
    }
    auto identity = ArrayPatternKeyIdentity(key);
    if (!identity) continue;
    if (!seen.insert(*identity).second) {
      check.diag.Error(
          loc,
          std::format("duplicate index key '{}' in array pattern", *identity),
          Subclause("10.9.1"));
    }
  }
}

}  // namespace delta
