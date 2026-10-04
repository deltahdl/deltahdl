#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_license.h"

namespace delta {
namespace {

// The subclause defining the spelling of `keyword`'s value. §34.5.28 and
// §34.5.29 write the same list, so what a report cites is the only thing that
// separates one keyword's reports from the other's.
std::string_view SyntaxSubclause(std::string_view keyword) {
  return keyword == kDecryptLicenseKeyword ? "34.5.28.1" : "34.5.29.1";
}

}  // namespace

void Preprocessor::ApplyLicense(const PragmaKeywordExpression& expr,
                                SourceLoc loc) {
  // A refusal speaks for the envelope it was met in, so it lapses once the
  // reading has left that envelope, whichever expression closed it.
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
  // §34.5.28.1 and §34.5.29.1 write the value as a library, an entry and a
  // feature, each against a string. A value written any other way names no
  // library to load, so there is no entry function for the feature it asks
  // about, and the expression states no licence for a tool to be held to.
  if (!license.stated) {
    diag_.Error(loc,
                std::string("protect pragma ")
                    .append(expr.keyword)
                    .append(" expression is written as a library, an entry "
                            "and a feature, each against a string"),
                Subclause(SyntaxSubclause(expr.keyword)));
    return;
  }
  // §34.5.28.2 and §34.5.29.2 put their question on meeting the expression in
  // an encrypted model, so a licence written in cleartext the tool is about to
  // encrypt is asking nothing of this run. That is the ENCRYPTION INPUT case
  // both subclauses open with: the expression is written inside a begin-end
  // pair so that it is encrypted into the output the author ships, and it
  // speaks to whoever reads that output rather than to whoever wrote it.
  if (!protect_envelopes_.InProtectedRegion()) return;
  // §34.5.29.2 asks its question before the model is executed, which is the
  // run's business once preprocessing is over.
  if (expr.keyword == kRuntimeLicenseKeyword) {
    runtime_licenses_.push_back({std::move(license), loc});
    return;
  }
  // §34.5.28.2 asks its question before the decrypted text is processed: the
  // library is loaded, its entry function called with the feature string, and
  // the value it returns compared with the match value.
  ProtectLicenseAnswer answer;
  if (config_.ask_license) {
    answer = config_.ask_license(license);
  } else {
    answer.why_not_called = "this reading loads no library";
  }
  if (ProtectLicenseGranted(license, answer)) return;
  diag_.Error(loc, ProtectLicenseRefusal(expr.keyword, license, answer),
              Subclause("34.5.28.2"));
  if (decryption_refused_depth_ == 0) {
    decryption_refused_depth_ = protect_envelopes_.DecryptionEnvelopeDepth();
  }
}

}  // namespace delta
