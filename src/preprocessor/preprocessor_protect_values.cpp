#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"
#include "preprocessor/protect_processing.h"

namespace delta {

void Preprocessor::ReadProtectKeyBlock(std::string_view text, SourceLoc loc,
                                       int depth) {
  std::string block;
  if (!ReadEncodedProtectValue(text, loc, &block)) return;
  std::string content;
  if (!DecryptProtectedBlock(
          block, ProtectKeyBlockKey(protect_keywords_, config_.protect_keys),
          &content, protect_keywords_.ValueOf(kKeyMethodKeyword).value)) {
    return;
  }
  bool was_recording = recording_origins_;
  bool was_reading_block = reading_key_block_;
  recording_origins_ = false;
  reading_key_block_ = true;
  ProcessSource(content, loc.file_id, depth + 1);
  recording_origins_ = was_recording;
  reading_key_block_ = was_reading_block;
  digest_target_ = {content, std::string(DigestBlockKeyInEffect())};
}

bool Preprocessor::TakeDigestDecryptKeyValue(std::string_view line,
                                             SourceLoc loc) {
  if (!digest_decrypt_key_value_next_) return false;
  digest_decrypt_key_value_next_ = false;
  std::string key;
  if (!ReadEncodedProtectValue(Trim(line), loc, &key)) return true;
  CheckDigestDesignationValue(kDigestDecryptKeyKeyword, key, loc);
  digest_decrypt_key_ = std::move(key);
  return true;
}

void Preprocessor::ReadProtectDigestBlock(std::string_view text,
                                          SourceLoc loc) {
  ProtectDigestTarget target = std::move(digest_target_);
  digest_target_ = ProtectDigestTarget();
  std::string block;
  if (!ReadEncodedProtectValue(text, loc, &block)) return;
  last_digest_block_check_ = CheckProtectDigestBlock(
      block, target, DigestMethodInEffect(),
      ProtectDigestKeyMethodInEffect(protect_keywords_).value);
  if (last_digest_block_check_ == ProtectDigestCheck::kAltered) {
    diag_.Error(loc,
                "protect pragma digest block disagrees with the block it "
                "follows, so one of the two was altered after encryption",
                Subclause("34.5.22"));
  }
}

bool Preprocessor::TakeDataDecryptKeyValue(std::string_view line,
                                           SourceLoc loc) {
  if (!data_decrypt_key_value_next_) return false;
  data_decrypt_key_value_next_ = false;
  std::string key;
  if (!ReadEncodedProtectValue(Trim(line), loc, &key)) return true;
  CheckDataKeyDesignationValue(kDataDecryptKeyKeyword, key, loc);
  data_decrypt_key_ = std::move(key);
  return true;
}

bool Preprocessor::TakeKeyPublicKeyValue(std::string_view line, SourceLoc loc) {
  if (!key_public_key_value_next_) return false;
  key_public_key_value_next_ = false;
  std::string value;
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kKeyPublicKeyKeyword, value);
  CheckKeyBlockDesignation(kKeyPublicKeyKeyword, value, loc);
  return true;
}

bool Preprocessor::TakeDataPublicKeyValue(std::string_view line,
                                          SourceLoc loc) {
  if (!data_public_key_value_next_) return false;
  data_public_key_value_next_ = false;
  std::string value;
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kDataPublicKeyKeyword, value);
  CheckDataKeyDesignationValue(kDataPublicKeyKeyword, value, loc);
  CheckDataDesignationAgreement(loc);
  return true;
}

bool Preprocessor::TakeDigestPublicKeyValue(std::string_view line,
                                            SourceLoc loc) {
  if (!digest_public_key_value_next_) return false;
  digest_public_key_value_next_ = false;
  std::string value;
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kDigestPublicKeyKeyword, value);
  CheckDigestDesignationValue(kDigestPublicKeyKeyword, value, loc);
  CheckDigestDesignationAgreement(loc);
  return true;
}

bool Preprocessor::ReadEncodedProtectValue(std::string_view text, SourceLoc loc,
                                           std::string* bytes) {
  ProtectEncoding encoding = ProtectEncodingInEffect();
  ProtectEncodedValueRead read = ReadProtectEncodedValue(text, encoding, bytes);
  if (read == ProtectEncodedValueRead::kSchemeUnavailable) {
    diag_.Error(loc,
                "protect pragma encoding names an enctype this implementation "
                "does not provide",
                Subclause("34.5.9.2"));
    return false;
  }
  if (read == ProtectEncodedValueRead::kNotWrittenInScheme) {
    diag_.Error(loc,
                "protect pragma value is not written in the encoding in effect",
                Subclause("34.5.9.2"));
    return false;
  }
  if (encoding.enctype == kRawEnctype && encoding.has_bytes &&
      encoding.bytes == bytes->size() + 1) {
    bytes->push_back('\n');
  }
  if (!ProtectEncodedValueHasStatedSize(encoding, bytes->size())) {
    diag_.Error(loc,
                "protect pragma value stands for a different number of bytes "
                "from the one the encoding in effect states",
                Subclause("34.5.9.2"));
    return false;
  }
  SpendEncodedValueSize();
  return true;
}

void Preprocessor::SpendEncodedValueSize() {
  ProtectKeywordValue held = protect_keywords_.ValueOf(kEncodingKeyword);
  if (held.defaulted) return;
  ProtectEncoding encoding = ParseProtectEncoding(held.value);
  if (!encoding.has_bytes) return;
  encoding.has_bytes = false;
  protect_keywords_.Apply(kEncodingKeyword, ProtectEncodingValue(encoding));
}

void Preprocessor::ReadProtectDataBlock(std::string_view text, SourceLoc loc,
                                        int depth, std::string& output) {
  if (decryption_refused_depth_ != 0) return;
  std::string block;
  if (!ReadEncodedProtectValue(text, loc, &block)) return;
  std::string region_key(ProtectKeyInEffect());
  std::string digest_key(DigestBlockKeyInEffect());
  data_decrypt_key_.clear();
  ProtectKeywordValue method = protect_keywords_.ValueOf(kDataMethodKeyword);
  if (!method.defaulted && !method.value.empty() &&
      method.value != kDataMethod && method.value != kDesCbcMethod) {
    diag_.Error(loc,
                "protect pragma data block states an encryption algorithm this "
                "implementation does not provide: " +
                    method.value,
                Subclause("34.5.11.2"));
    return;
  }
  std::string cleartext;
  if (!DecryptProtectedBlock(block, region_key, &cleartext, method.value)) {
    diag_.Error(loc,
                "protect pragma data block cannot be decrypted with the key "
                "supplied",
                Subclause("34.3.2"));
    return;
  }
  ProtectDigestTarget target{cleartext, std::move(digest_key)};
  digest_decrypt_key_.clear();
  std::string block_name = "<protected envelope at " +
                           std::string(src_mgr_.FilePath(loc.file_id)) + ":" +
                           std::to_string(loc.line) + ">";
  uint32_t block_id = src_mgr_.AddFile(std::move(block_name), cleartext);
  src_mgr_.MarkProtected(block_id);
  protect_envelope_source_ = block_id;
  if (!RecoveredTextLicensed(cleartext, block_id)) {
    decryption_refused_depth_ = protect_envelopes_.DecryptionEnvelopeDepth();
    return;
  }
  ReadRecoveredText(output);
  recovered_text_ = RecoveredText{std::move(cleartext), block_id, depth};
  digest_target_ = std::move(target);
}

void Preprocessor::ReadRecoveredText(std::string& output) {
  if (!recovered_text_.has_value()) return;
  RecoveredText held = std::move(*recovered_text_);
  recovered_text_.reset();
  output.append(ProcessSource(held.cleartext, held.block_id, held.depth));
}

bool Preprocessor::TookAnnouncedValue(std::string_view line, SourceLoc loc,
                                      int depth, std::string& output) {
  bool ends_envelope = protect_envelopes_.InProtectedRegion() &&
                       NamesBareKeyword(line, kEndDecryptionKeyword);
  if (gathering_block_ != ProtectBlockKind::kNone && !ends_envelope &&
      !StartsWithPragmaDirective(line)) {
    AppendGatheredProtectBlockLine(line);
    return true;
  }
  FinishGatheredProtectBlock(depth, output);
  if (ends_envelope) {
    EndAccumulatedProtectPragmas();
    ReadRecoveredText(output);
  }
  if (TakeKeyPublicKeyValue(line, loc)) return true;
  if (StartGatheredProtectBlock(line, loc)) return true;
  if (TakeDataDecryptKeyValue(line, loc)) return true;
  if (TakeDataPublicKeyValue(line, loc)) return true;
  if (TakeDigestPublicKeyValue(line, loc)) return true;
  return TakeDigestDecryptKeyValue(line, loc);
}

ProtectBlockKind Preprocessor::AnnouncedProtectBlockKind() const {
  if (key_block_value_next_) return ProtectBlockKind::kKey;
  if (data_block_value_next_) return ProtectBlockKind::kData;
  if (digest_block_value_next_) return ProtectBlockKind::kDigest;
  return ProtectBlockKind::kNone;
}

bool Preprocessor::StartGatheredProtectBlock(std::string_view line,
                                             SourceLoc loc) {
  ProtectBlockKind kind = AnnouncedProtectBlockKind();
  if (kind == ProtectBlockKind::kNone) return false;
  key_block_value_next_ = false;
  data_block_value_next_ = false;
  digest_block_value_next_ = false;
  if (StartsWithPragmaDirective(line)) return false;
  gathering_block_ = kind;
  gathering_block_loc_ = loc;
  gathering_block_text_.assign(GatheredBlockLine(line));
  return true;
}

void Preprocessor::AppendGatheredProtectBlockLine(std::string_view line) {
  gathering_block_text_.push_back('\n');
  gathering_block_text_.append(GatheredBlockLine(line));
}

std::string_view Preprocessor::GatheredBlockLine(std::string_view line) const {
  if (ProtectEncodingInEffect().enctype == kRawEnctype) return line;
  return Trim(line);
}

void Preprocessor::FinishGatheredProtectBlock(int depth, std::string& output) {
  ProtectBlockKind kind = gathering_block_;
  if (kind == ProtectBlockKind::kNone) return;
  std::string block = std::move(gathering_block_text_);
  SourceLoc loc = gathering_block_loc_;
  gathering_block_ = ProtectBlockKind::kNone;
  gathering_block_text_.clear();
  switch (kind) {
    case ProtectBlockKind::kKey:
      ReadProtectKeyBlock(block, loc, depth);
      return;
    case ProtectBlockKind::kData:
      ReadProtectDataBlock(block, loc, depth, output);
      return;
    default:
      ReadProtectDigestBlock(block, loc);
      return;
  }
}

}  // namespace delta
