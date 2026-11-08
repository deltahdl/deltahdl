#include "preprocessor/protect_viewport.h"

#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {
namespace {

bool WrittenAsString(std::string_view text) { return text.starts_with('"'); }

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
  std::string_view inside = value.substr(1, value.size() - 2);
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
  if (!named_object || !named_access) return {};
  viewport.stated = true;
  return viewport;
}

}  // namespace delta
