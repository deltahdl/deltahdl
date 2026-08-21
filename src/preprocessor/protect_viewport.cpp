#include "preprocessor/protect_viewport.h"

#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {
namespace {

// Whether `text` is written as a string. §22.5.1 spells a pragma_value four
// ways and only one of them is a string, so a value carrying no quotation
// marks around it is one of the other three however much it reads like the
// name a producer meant.
bool WrittenAsString(std::string_view text) {
  return text.size() >= 2 && text.front() == '"' && text.back() == '"';
}

// Takes the string written against one of the two names into `into`, and
// reports whether the expression was that name written that way.
bool TookSubkeyword(const ListedKeyword& listed, std::string_view name,
                    std::string* into) {
  if (listed.name != name) return false;
  if (!listed.has_value || !WrittenAsString(listed.value)) return false;
  *into = std::string(ProtectPragmaValueBody(listed.value));
  return true;
}

}  // namespace

ProtectViewport ParseProtectViewport(std::string_view value) {
  if (!IsParenthesizedPragmaValue(value)) return {};
  // The expressions of the list are what TopLevelKeywords walks, so the
  // parentheses announcing the list come off before the walk rather than
  // reaching it as characters of the first expression.
  std::string_view inside = value.substr(1);
  if (!inside.empty() && inside.back() == ')') inside.remove_suffix(1);
  ProtectViewport viewport;
  bool named_object = false;
  bool named_access = false;
  for (const ListedKeyword& listed : TopLevelKeywords(inside)) {
    named_object =
        TookSubkeyword(listed, kObjectSubkeyword, &viewport.object) ||
        named_object;
    named_access =
        TookSubkeyword(listed, kAccessSubkeyword, &viewport.access) ||
        named_access;
  }
  // Both, because §34.5.32.1 writes both. An expression naming one of them
  // describes an object nothing is permitted for, or permits something of no
  // object, and neither is what the subclause has a viewport say.
  if (!named_object || !named_access) return {};
  viewport.stated = true;
  return viewport;
}

}  // namespace delta
