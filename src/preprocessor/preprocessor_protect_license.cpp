#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_input_line.h"
#include "preprocessor/protect_license.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {
namespace {

std::string_view SyntaxSubclause(std::string_view keyword) {
  return keyword == kDecryptLicenseKeyword ? "34.5.28.1" : "34.5.29.1";
}

}  // namespace

void Preprocessor::ApplyLicense(const PragmaKeywordExpression& expr,
                                SourceLoc loc) {
  if (decryption_refused_depth_ >
      protect_envelopes_.DecryptionEnvelopeDepth()) {
    decryption_refused_depth_ = 0;
  }
  if (expr.keyword != kDecryptLicenseKeyword &&
      expr.keyword != kRuntimeLicenseKeyword) {
    return;
  }
  ProtectLicense license =
      ParseProtectLicense(expr.value.empty() ? expr.value_list : expr.value);
  if (!license.stated) {
    diag_.Error(loc,
                std::string("protect pragma ")
                    .append(expr.keyword)
                    .append(" expression is written as a library, an entry "
                            "and a feature, each against a string"),
                Subclause(SyntaxSubclause(expr.keyword)));
    return;
  }
  if (!protect_envelopes_.InProtectedRegion()) return;
  if (expr.keyword == kRuntimeLicenseKeyword) {
    runtime_licenses_.push_back({std::move(license), loc});
    return;
  }
}

bool Preprocessor::AskDecryptLicense(const ProtectLicense& license,
                                     SourceLoc loc) {
  ProtectLicenseAnswer answer;
  if (config_.ask_license) {
    answer = config_.ask_license(license);
  } else {
    answer.why_not_called = "this reading loads no library";
  }
  if (ProtectLicenseGranted(license, answer)) return true;
  diag_.Error(loc,
              ProtectLicenseRefusal(kDecryptLicenseKeyword, license, answer),
              Subclause("34.5.28.2"));
  return false;
}

bool Preprocessor::LicencesOfDirectiveGranted(std::string_view body,
                                              uint32_t block_id,
                                              uint32_t line_num,
                                              int* sealed_inside) {
  bool granted = true;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name == kBeginDecryptionKeyword) {
      ++*sealed_inside;
    } else if (listed.name == kEndDecryptionKeyword) {
      --*sealed_inside;
    } else if (*sealed_inside == 0 && listed.name == kDecryptLicenseKeyword) {
      ProtectLicense license = ParseProtectLicense(listed.value);
      if (!license.stated) continue;
      if (!AskDecryptLicense(license, SourceLoc{block_id, line_num, 1})) {
        granted = false;
      }
    }
  }
  return granted;
}

bool Preprocessor::RecoveredTextLicensed(std::string_view cleartext,
                                         uint32_t block_id) {
  bool granted = true;
  int sealed_inside = 0;
  uint32_t line_num = 0;
  for (std::string_view line : SplitLines(cleartext)) {
    ++line_num;
    std::string_view body;
    if (!ProtectPragmaLine(line, &body)) continue;
    if (!LicencesOfDirectiveGranted(body, block_id, line_num, &sealed_inside)) {
      granted = false;
    }
  }
  return granted;
}

}  // namespace delta
