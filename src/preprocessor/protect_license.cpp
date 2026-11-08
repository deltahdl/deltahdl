#include "preprocessor/protect_license.h"

#include <cstdint>
#include <limits>
#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {
namespace {

bool WrittenAsString(std::string_view text) { return text.starts_with('"'); }

bool TookString(const ListedKeyword& listed, std::string_view name,
                std::string* into) {
  if (listed.name != name) return false;
  if (!listed.has_value || !WrittenAsString(listed.value)) return false;
  *into = std::string(ProtectPragmaValueBody(listed.value));
  return true;
}

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
  std::string_view inside = value.substr(1, value.size() - 2);
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
  if (!named_library || !named_entry || !named_feature) return {};
  license.stated = true;
  return license;
}

bool ProtectLicenseGranted(const ProtectLicense& license,
                           const ProtectLicenseAnswer& answer) {
  return answer.called && answer.returned >= 0 &&
         static_cast<uint64_t>(answer.returned) == license.match;
}

std::string ProtectLicenseRefusal(std::string_view keyword,
                                  const ProtectLicense& license,
                                  const ProtectLicenseAnswer& answer) {
  std::string message("protect pragma ");
  message.append(keyword).append(" entry function \"").append(license.entry);
  message.append("\" in \"").append(license.library).append("\"");
  if (answer.called) {
    message.append(" returned ")
        .append(std::to_string(answer.returned))
        .append(" for feature \"")
        .append(license.feature)
        .append("\", not the match value ")
        .append(std::to_string(license.match));
  } else {
    message.append(" was not called for feature \"")
        .append(license.feature)
        .append("\": ")
        .append(answer.why_not_called);
  }
  message.append(keyword == kDecryptLicenseKeyword
                     ? ", so this tool is not licensed to decrypt the model"
                     : ", so this tool is not licensed to execute the model");
  return message;
}

}  // namespace delta
