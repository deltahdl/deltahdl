#include "preprocessor/protect_license.h"

#include <cstdint>
#include <limits>
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

// Takes the string written against one of the five names into `into`, and
// reports whether the expression was that name written that way.
bool TookString(const ListedKeyword& listed, std::string_view name,
                std::string* into) {
  if (listed.name != name) return false;
  if (!listed.has_value || !WrittenAsString(listed.value)) return false;
  *into = std::string(ProtectPragmaValueBody(listed.value));
  return true;
}

// The same for the one name written against a <number>. Digits are the whole of
// that spelling, so text carrying anything else states no number, and a number
// too large to be held states none either: a value the reading rounded or
// wrapped would be compared against the entry function's return as though the
// text had written it.
bool TookNumber(const ListedKeyword& listed, std::string_view name,
                uint64_t* into) {
  if (listed.name != name) return false;
  if (!listed.has_value || listed.value.empty()) return false;
  uint64_t number = 0;
  for (char c : listed.value) {
    if (c < '0' || c > '9') return false;
    auto digit = static_cast<uint64_t>(c - '0');
    if (number > (std::numeric_limits<uint64_t>::max() - digit) / 10) {
      return false;
    }
    number = (number * 10) + digit;
  }
  *into = number;
  return true;
}

}  // namespace

ProtectLicense ParseProtectLicense(std::string_view value) {
  if (!IsParenthesizedPragmaValue(value)) return {};
  // The expressions of the list are what TopLevelKeywords walks, so the
  // parentheses announcing the list come off before the walk rather than
  // reaching it as characters of the first expression.
  std::string_view inside = value.substr(1);
  if (!inside.empty() && inside.back() == ')') inside.remove_suffix(1);
  ProtectLicense license;
  bool named_library = false;
  bool named_entry = false;
  bool named_feature = false;
  for (const ListedKeyword& listed : TopLevelKeywords(inside)) {
    named_library = TookString(listed, kLibrarySubkeyword, &license.library) ||
                    named_library;
    named_entry =
        TookString(listed, kEntrySubkeyword, &license.entry) || named_entry;
    named_feature = TookString(listed, kFeatureSubkeyword, &license.feature) ||
                    named_feature;
    license.has_exit =
        TookString(listed, kExitSubkeyword, &license.exit) || license.has_exit;
    license.has_match = TookNumber(listed, kMatchSubkeyword, &license.match) ||
                        license.has_match;
  }
  // All three, because both syntax lines write all three outside the brackets
  // that mark the other two optional. A list short of one of them names a
  // library with no entry point to call in it, or an entry point with no
  // feature to ask about, and §34.5.28.2 spends all three in the one sentence
  // that carries out the check.
  if (!named_library || !named_entry || !named_feature) return {};
  license.stated = true;
  return license;
}

}  // namespace delta
