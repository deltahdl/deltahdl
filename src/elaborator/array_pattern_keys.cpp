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

namespace {

// What two array pattern keys are the same key by. §10.9's array keys are
// constant expressions, so what a key names is its value: `3` and `N-1` with N
// of 4 name the element between them once, not twice. A key that does not fold
// here is answered for by how it was written, which still tells apart the two
// halves of a key written the same way twice. Nothing for a key that neither
// folds nor was written as a single name or literal -- there is no ground to
// call two of those the same, and calling them so would report every pair of
// them as a duplicate.
std::optional<std::string> ArrayPatternKeyIdentity(const Expr* key) {
  auto value = ConstEvalInt(key);
  if (value) return std::to_string(*value);
  if (key->text.empty()) return std::nullopt;
  return std::string(key->text);
}

}  // namespace

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
