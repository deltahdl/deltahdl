#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

bool DesignatesKeyBlockKey(const PragmaKeywordExpression& expr) {
  if (!expr.has_value || expr.value.empty()) return false;
  return IsProtectKeyBlockDesignationKeyword(expr.keyword);
}

bool AnnouncesPublicKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kKeyPublicKeyKeyword && !expr.has_value;
}

bool AnnouncesKeyBlock(const PragmaKeywordExpression& expr) {
  return expr.keyword == kKeyBlockKeyword && !expr.has_value;
}

bool AnnouncesDataDecryptKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDataDecryptKeyKeyword && !expr.has_value;
}

bool AnnouncesDataPublicKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDataPublicKeyKeyword && !expr.has_value;
}

bool AnnouncesDigestPublicKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDigestPublicKeyKeyword && !expr.has_value;
}

bool AnnouncesDigestDecryptKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDigestDecryptKeyKeyword && !expr.has_value;
}

bool AnnouncesDigestBlock(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDigestBlockKeyword && !expr.has_value;
}

bool AnnouncesDataBlock(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDataBlockKeyword && !expr.has_value;
}

}  // namespace

void Preprocessor::CheckKeyBlockDesignation(std::string_view keyword,
                                            std::string_view value,
                                            SourceLoc loc) {
  if (value.empty()) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kKeyKeyownerKeyword);
  if (!protect_key_block_designations_.Record(owner.value, keyword, value)) {
    diag_.Error(loc,
                "protect pragma writes one value against both of the names "
                "that designate a key of the key_keyowner in effect",
                Subclause("34.5.23"));
  }
  if (ProtectKeyBlockDesignationsAgree(protect_keywords_,
                                       config_.protect_keys) ==
      ProtectKeyAgreement::kDifferentKeys) {
    diag_.Error(loc,
                "protect pragma key_public_key and key_keyname designate "
                "different keys of the key_keyowner in effect",
                Subclause("34.5.26"));
  }
}

void Preprocessor::ApplyKeyBlockKeywords(const PragmaKeywordExpression& expr,
                                         SourceLoc loc) {
  if (DesignatesKeyBlockKey(expr)) {
    CheckKeyBlockDesignation(expr.keyword, ProtectPragmaValueBody(expr.value),
                             loc);
  }
  if (AnnouncesPublicKey(expr) && protect_envelopes_.InProtectedRegion()) {
    key_public_key_value_next_ = true;
  }
}

void Preprocessor::ApplyAnnouncedBlockKeywords(
    const PragmaKeywordExpression& expr) {
  if (!protect_envelopes_.InProtectedRegion()) return;
  if (AnnouncesKeyBlock(expr)) key_block_value_next_ = true;
  if (AnnouncesDataDecryptKey(expr)) data_decrypt_key_value_next_ = true;
  if (AnnouncesDataPublicKey(expr)) data_public_key_value_next_ = true;
  if (AnnouncesDigestPublicKey(expr)) digest_public_key_value_next_ = true;
  if (AnnouncesDigestDecryptKey(expr)) digest_decrypt_key_value_next_ = true;
  if (AnnouncesDataBlock(expr)) data_block_value_next_ = true;
  if (AnnouncesDigestBlock(expr) && !digest_target_.cleartext.empty()) {
    digest_block_value_next_ = true;
  }
}

void Preprocessor::CheckDataDesignationAgreement(SourceLoc loc) {
  if (ProtectDataDesignationsAgree(protect_keywords_, config_.protect_keys) !=
      ProtectKeyAgreement::kDifferentKeys) {
    return;
  }
  diag_.Error(loc,
              "protect pragma data_public_key and data_keyname designate "
              "different keys of the data_keyowner in effect",
              Subclause("34.5.13"));
}

void Preprocessor::CheckDigestDesignationAgreement(SourceLoc loc) {
  if (ProtectDigestDesignationsAgree(protect_keywords_, config_.protect_keys) !=
      ProtectKeyAgreement::kDifferentKeys) {
    return;
  }
  diag_.Error(loc,
              "protect pragma digest_public_key and digest_keyname designate "
              "different keys of the digest_keyowner in effect",
              Subclause("34.5.19"));
}

bool Preprocessor::ReportDelimiterWrittenWithValue(
    const PragmaKeywordExpression& expr, SourceLoc loc) {
  if (expr.keyword == kBeginEncryptionKeyword &&
      !OpensEncryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma begin keyword is written on its own and "
                "takes no pragma_value",
                Subclause("34.5.1.1"));
    return true;
  }
  if (expr.keyword == kEndEncryptionKeyword &&
      !ClosesEncryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma end keyword is written on its own and takes "
                "no pragma_value",
                Subclause("34.5.2.1"));
    return true;
  }
  if (expr.keyword == kBeginDecryptionKeyword &&
      !OpensDecryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma begin_protected keyword is written on its own "
                "and takes no pragma_value",
                Subclause("34.5.3.1"));
    return true;
  }
  if (expr.keyword == kEndDecryptionKeyword &&
      !ClosesDecryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma end_protected keyword is written on its own "
                "and takes no pragma_value",
                Subclause("34.5.4.1"));
    return true;
  }
  return false;
}

void Preprocessor::ApplyProtectKeywords(
    const std::vector<PragmaKeywordExpression>& keywords, SourceLoc loc) {
  for (const PragmaKeywordExpression& expr : keywords) {
    if (ReportDelimiterWrittenWithValue(expr, loc)) continue;
    if (expr.keyword == kResetKeyword && !expr.has_value) {
      ResetPragma(kProtectPragmaName);
      continue;
    }
    if (expr.has_value) {
      protect_keywords_.Apply(
          expr.keyword, expr.value.empty() ? expr.value_list : expr.value);
    }
    if (!protect_envelopes_.Apply(expr.keyword, loc)) {
      diag_.Error(loc,
                  "protect pragma nests decryption envelopes more deeply than "
                  "this implementation processes",
                  Subclause::None());
      continue;
    }
    if (ClosesDecryptionEnvelope(expr.keyword, expr.has_value)) {
      EndAccumulatedProtectPragmas();
    }
    CheckDataKeyname(expr, loc);
    CheckDigestKeyname(expr, loc);
    CheckKeyKeyname(expr, loc);
    CheckKeyDesignation(expr, loc);
    CheckDigestDesignation(expr, loc);
    ApplyKeyBlockKeywords(expr, loc);
    ApplyAnnouncedBlockKeywords(expr);
    ApplyViewport(expr, loc);
    ApplyLicense(expr, loc);
  }
}

}  // namespace delta
