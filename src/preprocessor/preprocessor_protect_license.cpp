#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_license.h"

namespace delta {
namespace {

// The subclause defining the spelling of `keyword`'s value, and the one
// defining what a tool does with it. §34.5.28 and §34.5.29 write the same list
// and put the same question, so what a report cites is the only thing that
// separates one keyword's reports from the other's.
std::string_view SyntaxSubclause(std::string_view keyword) {
  return keyword == kDecryptLicenseKeyword ? "34.5.28.1" : "34.5.29.1";
}

std::string_view DescriptionSubclause(std::string_view keyword) {
  return keyword == kDecryptLicenseKeyword ? "34.5.28.2" : "34.5.29.2";
}

// What the tool goes on to do with the model it never asked a licence for.
// §34.5.28.2 has an unlicensed tool perform no decryption, and §34.5.29.2 has
// it not begin execution, so those are the two things a run that skipped the
// check does anyway.
std::string_view WhatIsDoneUnasked(std::string_view keyword) {
  return keyword == kDecryptLicenseKeyword ? "decrypts the model"
                                           : "goes on to execute the model";
}

}  // namespace

void Preprocessor::ApplyLicense(const PragmaKeywordExpression& expr,
                                SourceLoc loc) {
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
  // The check itself is performed by nothing, and the expression is reported
  // for that reason. §34.5.28.2 has the tool load the library the value names,
  // call the entry function in it with the feature string, compare what comes
  // back against the match value, and refuse to decrypt where the two differ;
  // §34.5.29.2 asks the same before the model is executed. This tool loads no
  // library named by a text it reads, and #3443 carries what it would take to:
  // loading a shared object a source file chooses is a capability this program
  // has nowhere else, and giving it one is a decision about what a source file
  // may make the tool do rather than about protect pragmas.
  //
  // Both subclauses close with a NOTE saying the mechanism provides only
  // limited security, the end user holding the shared library and being able to
  // produce an equivalent one that returns a 0 and avoids the check. So what an
  // author is owed here is an honest account of what the run did, and silence
  // is the one answer that leaves the author believing the licence was
  // consulted.
  diag_.Warning(loc,
                std::string("protect pragma ")
                    .append(expr.keyword)
                    .append(" expression is not acted on: this tool loads no "
                            "library a source text names, so the entry "
                            "function \"")
                    .append(license.entry)
                    .append("\" in \"")
                    .append(license.library)
                    .append("\" is not called for feature \"")
                    .append(license.feature)
                    .append("\" and this run ")
                    .append(WhatIsDoneUnasked(expr.keyword))
                    .append(" unlicensed"),
                Subclause(DescriptionSubclause(expr.keyword)));
}

}  // namespace delta
