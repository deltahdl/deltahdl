#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

bool Preprocessor::KeynameCarriedByKeyBlock(std::string_view owner,
                                            std::string_view name) {
  std::string key(owner);
  key.push_back('\0');
  key.append(name);
  if (reading_key_block_) {
    names_carried_by_key_blocks_.insert(std::move(key));
    return true;
  }
  return names_carried_by_key_blocks_.contains(key);
}

void Preprocessor::CheckDataKeyname(const PragmaKeywordExpression& expr,
                                    SourceLoc loc) {
  if (expr.keyword != kDataKeynameKeyword || !expr.has_value) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kDataKeyownerKeyword);
  if (KeynameCarriedByKeyBlock(owner.value,
                               ProtectPragmaValueBody(expr.value))) {
    return;
  }
  if (!ProtectKeynameReachesNoKey(config_.protect_keys, owner.value,
                                  ProtectPragmaValueBody(expr.value))) {
    return;
  }
  diag_.Error(loc,
              "protect pragma data_keyname names no key held by the "
              "data_keyowner in effect",
              Subclause("34.5.12"));
}

void Preprocessor::CheckDigestKeyname(const PragmaKeywordExpression& expr,
                                      SourceLoc loc) {
  if (expr.keyword != kDigestKeynameKeyword || !expr.has_value) return;
  ProtectKeywordValue owner = protect_keywords_.DigestKeyownerInEffect();
  if (KeynameCarriedByKeyBlock(owner.value,
                               ProtectPragmaValueBody(expr.value))) {
    return;
  }
  if (!ProtectKeynameReachesNoKey(config_.protect_keys, owner.value,
                                  ProtectPragmaValueBody(expr.value))) {
    return;
  }
  diag_.Error(loc,
              "protect pragma digest_keyname names no key held by the "
              "digest_keyowner in effect",
              Subclause("34.5.18"));
}

void Preprocessor::CheckKeyKeyname(const PragmaKeywordExpression& expr,
                                   SourceLoc loc) {
  if (expr.keyword != kKeyKeynameKeyword || !expr.has_value) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kKeyKeyownerKeyword);
  if (!ProtectKeynameReachesNoKey(config_.protect_keys, owner.value,
                                  ProtectPragmaValueBody(expr.value))) {
    return;
  }
  diag_.Error(loc,
              "protect pragma key_keyname names no key held by the "
              "key_keyowner in effect",
              Subclause("34.5.25"));
}

void Preprocessor::CheckDataKeyDesignationValue(std::string_view keyword,
                                                std::string_view value,
                                                SourceLoc loc) {
  if (value.empty()) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kDataKeyownerKeyword);
  if (!protect_key_designations_.Record(owner.value, keyword, value)) {
    diag_.Error(loc,
                "protect pragma writes one value against two of the names that "
                "designate a key of the data_keyowner in effect",
                Subclause("34.5.10"));
  }
}

void Preprocessor::CheckKeyDesignation(const PragmaKeywordExpression& expr,
                                       SourceLoc loc) {
  if (!expr.has_value || expr.value.empty()) return;
  if (!IsProtectKeyDesignationKeyword(expr.keyword)) return;
  CheckDataKeyDesignationValue(expr.keyword, ProtectPragmaValueBody(expr.value),
                               loc);
  CheckDataDesignationAgreement(loc);
}

void Preprocessor::CheckDigestDesignationValue(std::string_view keyword,
                                               std::string_view value,
                                               SourceLoc loc) {
  if (value.empty()) return;
  ProtectKeywordValue owner = protect_keywords_.DigestKeyownerInEffect();
  if (!protect_digest_designations_.Record(owner.value, keyword, value)) {
    diag_.Error(loc,
                "protect pragma writes one value against two of the names that "
                "designate a key of the digest_keyowner in effect",
                Subclause("34.5.16"));
  }
}

void Preprocessor::CheckDigestDesignation(const PragmaKeywordExpression& expr,
                                          SourceLoc loc) {
  if (!expr.has_value || expr.value.empty()) return;
  if (!IsProtectDigestDesignationKeyword(expr.keyword)) return;
  CheckDigestDesignationValue(expr.keyword, ProtectPragmaValueBody(expr.value),
                              loc);
  CheckDigestDesignationAgreement(loc);
}

}  // namespace delta
