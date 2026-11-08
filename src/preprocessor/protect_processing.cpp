#include "preprocessor/protect_processing.h"

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_designation_reports.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_input_line.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"
#include "preprocessor/protect_region_lines.h"

namespace delta {

struct ReadRegion {
  std::string_view opening_line;
  SourceLoc opened;
  std::string opening_directive;
  std::string source_body;
  std::string body;
  RegionKeyReader written_inside;
};

namespace {

void ReportUnprovidedDataMethod(const RegionKeyReader& in_effect,
                                DiagEngine* diag, uint32_t file_id) {
  if (diag == nullptr) return;
  std::string_view stated = ProtectPragmaValueBody(in_effect.data_method);
  if (stated.empty() || stated == kDataMethod || stated == kDesCbcMethod) {
    return;
  }
  std::string message(
      "protect pragma data_method asks for an encryption algorithm this "
      "implementation does not provide: ");
  message.append(stated);
  message.append(
      ", which IEEE 1800-2023 Table 34-3 does not require of every "
      "implementation");
  diag->Error(LineOf(file_id, in_effect.data_method_line), message,
              Subclause("34.5.11.2"));
}

bool LiftedIntoTheClear(std::string_view line, bool previously_protected) {
  if (previously_protected) return false;
  return !KeywordSingleValueOnLine(line, kAuthorKeyword).empty() ||
         !KeywordSingleValueOnLine(line, kAuthorInfoKeyword).empty() ||
         !KeywordSingleValueOnLine(line, kCommentKeyword).empty();
}

bool IsLiftedExpression(const ListedKeyword& listed) {
  if (!listed.has_value || IsParenthesizedPragmaValue(listed.value)) {
    return false;
  }
  return listed.name == kAuthorKeyword || listed.name == kAuthorInfoKeyword ||
         listed.name == kCommentKeyword;
}

bool RequestsADigest(std::string_view line, bool previously_protected) {
  return !previously_protected && NamesKeyword(line, kDigestBlockKeyword);
}

std::string LeftInTheBlock(std::string_view line) {
  std::string_view body;
  ProtectPragmaLine(line, &body);
  std::vector<std::string_view> kept;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (!IsLiftedExpression(listed) && listed.name != kDigestBlockKeyword) {
      kept.push_back(ListedExpressionText(body, listed));
    }
  }
  return ProtectDirectiveWriting(kept);
}

bool HoldsAnAuthorsKey(std::string_view line, const RegionKeyReader& inside) {
  return inside.encoded_data_decrypt_key_next ||
         inside.encoded_digest_decrypt_key_next ||
         NamesBareKeyword(line, kDataDecryptKeyKeyword) ||
         NamesBareKeyword(line, kDigestDecryptKeyKeyword);
}

void AppendEnvelopeExpressions(std::string_view line, uint32_t line_num,
                               bool previously_protected, ReadRegion* region) {
  if (!HoldsAnAuthorsKey(line, region->written_inside)) {
    region->body.append(LiftedIntoTheClear(line, previously_protected) ||
                                RequestsADigest(line, previously_protected)
                            ? LeftInTheBlock(line)
                            : std::string(line));
  }
  TakeKeyNamesOutsideProtectedBlock(line, line_num, previously_protected,
                                    &region->written_inside);
}

void AppendEnvelopeLine(std::string_view line, uint32_t line_num,
                        bool previously_protected, ReadRegion* region) {
  region->source_body.append(line);
  AppendEnvelopeExpressions(line, line_num, previously_protected, region);
}

void ReadOutsideRegion(std::string directive, uint32_t line_num,
                       RegionKeyReader* in_effect) {
  if (directive.empty()) return;
  std::string_view held = in_effect->Hold(std::move(directive));
  TakeKeyNamesOutsideProtectedBlock(held, line_num, false, in_effect);
}

void ReadIntoRegion(std::string directive, uint32_t line_num,
                    RegionKeyReader* in_effect, ReadRegion* region) {
  if (directive.empty()) return;
  std::string_view held = in_effect->Hold(std::move(directive));
  TakeKeyNamesOutsideProtectedBlock(held, line_num, false, in_effect);
  AppendEnvelopeExpressions(held, line_num, false, region);
}

std::string_view RegionKey(const RegionKeyNames& names,
                           std::string_view exchange_key,
                           const ProtectKeyList& keys) {
  if (keys.Empty()) return exchange_key;
  std::string_view owner = ProtectPragmaValueBody(names.data_keyowner);
  std::string_view under_name =
      keys.KeyFor(owner, ProtectPragmaValueBody(names.data_keyname));
  if (!under_name.empty()) return under_name;
  return keys.KeyFor(owner, names.data_public_key);
}

std::string_view ProvidedCipher(std::string_view stated) {
  return stated == kDesCbcMethod ? stated : std::string_view{};
}

ProtectKeyBlockRequests DesignatedKeyBlocks(const RegionKeyNames& names,
                                            uint32_t closing_line,
                                            std::string_view data_method) {
  ProtectKeyBlockRequests requests;
  if (!names.key_keyname.empty()) {
    requests.Designate(names.key_keyowner, names.key_keyname,
                       DataDecryptionInEffect(names, data_method),
                       closing_line);
  } else if (!names.key_public_key.empty()) {
    requests.DesignatePublicKey(names.key_keyowner, names.key_public_key,
                                DataDecryptionInEffect(names, data_method),
                                closing_line);
  }
  return requests;
}

void ReportUnavailableDigestMethod(const RegionKeyReader& in_effect,
                                   DiagEngine* diag, uint32_t file_id) {
  if (diag == nullptr || !in_effect.digest_requested) return;
  std::string_view stated = ProtectPragmaValueBody(in_effect.digest_method);
  if (stated.empty() || ProtectDigestIsAvailable(stated)) return;
  std::string message(
      "protect pragma digest_method asks for a message digest algorithm this "
      "implementation does not provide: ");
  message.append(stated);
  message.append(
      ", which IEEE 1800-2023 Table 34-4 does not require of every "
      "implementation");
  diag->Error(LineOf(file_id, in_effect.digest_method_line), message,
              Subclause("34.5.21.2"));
}

void ReportUnprovidedKeyMethod(const RegionKeyReader& in_effect,
                               const RegionEncryption& how, DiagEngine* diag,
                               uint32_t file_id) {
  if (diag == nullptr || how.key_blocks.directives.empty()) return;
  std::string_view stated = ProtectPragmaValueBody(in_effect.key_method);
  if (stated.empty() || stated == kDataMethod || stated == kDesCbcMethod) {
    return;
  }
  std::string message(
      "protect pragma key_method asks for an encryption algorithm this "
      "implementation does not provide: ");
  message.append(stated);
  message.append(
      ", which IEEE 1800-2023 Table 34-3 does not require of every "
      "implementation");
  diag->Error(LineOf(file_id, in_effect.key_method_line), message,
              Subclause("34.5.24.2"));
}

void ReportKeynamesReachingNoKey(const RegionKeyReader& in_effect,
                                 const ProtectKeyList& keys, DiagEngine* diag,
                                 uint32_t file_id) {
  if (diag == nullptr) return;
  const RegionKeyNames& names = in_effect.names;
  std::string_view data_owner = ProtectPragmaValueBody(names.data_keyowner);
  if (ProtectKeynameReachesNoKey(keys, data_owner,
                                 ProtectPragmaValueBody(names.data_keyname))) {
    diag->Error(LineOf(file_id, in_effect.data_keyname_line),
                "protect pragma data_keyname names no key held by the "
                "data_keyowner in effect",
                Subclause("34.5.12"));
  }
  std::string_view digest_owner = ProtectPragmaValueBody(names.digest_keyowner);
  if (digest_owner.empty()) digest_owner = data_owner;
  if (ProtectKeynameReachesNoKey(
          keys, digest_owner, ProtectPragmaValueBody(names.digest_keyname))) {
    diag->Error(LineOf(file_id, in_effect.digest_keyname_line),
                "protect pragma digest_keyname names no key held by the "
                "digest_keyowner in effect",
                Subclause("34.5.18"));
  }
  if (ProtectKeynameReachesNoKey(keys,
                                 ProtectPragmaValueBody(names.key_keyowner),
                                 ProtectPragmaValueBody(names.key_keyname))) {
    diag->Error(LineOf(file_id, in_effect.key_keyname_line),
                "protect pragma key_keyname names no key held by the "
                "key_keyowner in effect",
                Subclause("34.5.25"));
  }
}

ProtectDigestBlockPolicy DigestPolicyFor(const RegionKeyReader& in_effect) {
  ProtectDigestBlockPolicy policy;
  policy.requested = in_effect.digest_requested;
  policy.method =
      in_effect.digest_method.empty()
          ? std::string(kDefaultDigestMethod)
          : std::string(ProtectPragmaValueBody(in_effect.digest_method));
  policy.stated_method = std::string(in_effect.digest_method);
  policy.key_method = std::string(in_effect.digest_key_method);
  policy.cipher = std::string(ProtectPragmaValueBody(
      in_effect.digest_key_method.empty() ? in_effect.data_method
                                          : in_effect.digest_key_method));
  policy.keyname = std::string(in_effect.names.digest_keyname);
  return policy;
}

static void UnderNamedKey(RegionEncryption& how,
                          const RegionKeyReader& in_effect,
                          std::string_view named, const ProtectKeyList& keys) {
  how.key = named;
  std::string_view own = RegionDigestKey(in_effect.names, keys);
  how.digest.key = own.empty() ? named : own;
}

RegionEncryption RegionEncryptionFor(const RegionKeyReader& in_effect,
                                     const ReadRegion& region,
                                     std::string_view exchange_key,
                                     const ProtectKeyList& keys,
                                     uint32_t closing_line) {
  RegionEncryption how;
  how.digest = DigestPolicyFor(in_effect);
  std::string_view named = RegionKey(in_effect.names, exchange_key, keys);
  ProtectKeyBlockRequests requests =
      region.written_inside.key_blocks.Empty()
          ? DesignatedKeyBlocks(in_effect.names, closing_line,
                                ProtectPragmaValueBody(in_effect.data_method))
          : region.written_inside.key_blocks;
  if (!named.empty() && requests.Empty()) {
    UnderNamedKey(how, in_effect, named, keys);
    return how;
  }
  requests.UseKeyMethod(
      ProvidedCipher(ProtectPragmaValueBody(in_effect.key_method)));
  std::string_view digest_key = in_effect.digest_decrypt_key.empty()
                                    ? in_effect.data_decrypt_key
                                    : in_effect.digest_decrypt_key;
  std::string_view data_key =
      in_effect.data_decrypt_key.empty() ? named : in_effect.data_decrypt_key;
  how.key_blocks = ProtectKeyBlocksFor(
      requests, ProtectKeyBlockRegion{region.body, data_key, digest_key}, keys,
      EnvelopeEncodings(region.written_inside.encoding), how.digest);
  if (how.key_blocks.data_key.empty() && !named.empty()) {
    how.key_blocks = ProtectKeyBlocks{};
    UnderNamedKey(how, in_effect, named, keys);
    return how;
  }
  how.key = how.key_blocks.data_key;
  how.digest.key = how.key_blocks.digest_key;
  return how;
}

std::string ClosedRegionText(const ReadRegion& region,
                             const RegionKeyReader& in_effect,
                             std::string_view line,
                             const DelimiterMatch& delimiter,
                             const RegionEncryption& how) {
  if (how.key.empty()) {
    std::string text(region.opening_line);
    text.append(region.source_body).append(line);
    return text;
  }
  std::string closing_directive =
      ClosingDirectiveOf(line, delimiter, kEndDecryptionKeyword);
  EncryptionEnvelope envelope;
  envelope.begin_directive = region.opening_directive;
  envelope.body = region.body;
  envelope.end_directive = closing_directive;
  envelope.author = region.written_inside.author;
  envelope.author_info = region.written_inside.author_info;
  envelope.comment_directives = region.written_inside.comment_directives;
  envelope.names = in_effect.names;
  envelope.digest_method = in_effect.digest_method;
  envelope.digest_key_method = in_effect.digest_key_method;
  envelope.key_method = in_effect.key_method;
  envelope.data_method = in_effect.data_method;
  envelope.requested_encoding = region.written_inside.encoding;
  return DecryptionEnvelopeText(envelope, how);
}

void ReportClosedRegion(const RegionKeyReader& in_effect,
                        const RegionEncryption& how, const ProtectKeyList& keys,
                        DiagEngine* diag, SourceLoc opened) {
  if (diag != nullptr && how.key.empty()) {
    diag->Error(opened,
                "protect pragma encryption envelope has no key to be "
                "encrypted under, so it is written out unencrypted",
                Subclause("34.3.1"));
  }
  uint32_t file_id = opened.file_id;
  if (diag != nullptr && how.key_blocks.data_changed_line != 0) {
    diag->Error(LineOf(file_id, how.key_blocks.data_changed_line),
                "protect pragma data decryption expressions change value "
                "between the key_block pragma expressions of one encryption "
                "envelope",
                Subclause("34.5.27"));
  }
  ReportUnprovidedDataMethod(in_effect, diag, file_id);
  ReportUnavailableDigestMethod(in_effect, diag, file_id);
  ReportUnprovidedKeyMethod(in_effect, how, diag, file_id);
  ReportKeynamesReachingNoKey(in_effect, keys, diag, file_id);
  if (diag == nullptr) return;
  ReportRepeatedDesignations(in_effect, diag, opened);
  ReportDisagreeingDesignations(in_effect.names, keys, diag, opened);
}

bool SetAsideRejectedPragmaLine(std::string_view line, SourceLoc loc,
                                bool in_envelope, DiagEngine* diag,
                                std::string* transformed) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body) || body.contains('`')) return false;
  std::string text = std::string(kProtectPragmaName) + " " + std::string(body);
  std::string_view error = ReadPragmaDirective(text).error;
  if (error.empty()) return false;
  if (diag != nullptr) {
    diag->Error(loc, std::string(error), Subclause("22.11"));
  }
  if (!in_envelope) transformed->append(line);
  return true;
}

}  // namespace

struct EnvelopeEncryptionState {
  std::string exchange_key;
  ProtectKeyList keys;
  DiagEngine* diag = nullptr;
  ReadRegion region;
  RegionKeyReader in_effect;
  PreviouslyProtectedBlock previously_protected;
  bool in_envelope = false;
  bool in_block_comment = false;
};

namespace {

bool CarriedAsComment(EnvelopeEncryptionState& state, std::string_view line,
                      std::string* transformed) {
  const bool kInComment = state.in_block_comment;
  state.in_block_comment = BlockCommentOpenAfter(line, state.in_block_comment);
  if (!kInComment) return false;
  if (state.in_envelope) {
    state.region.source_body.append(line);
    state.region.body.append(line);
  } else {
    transformed->append(line);
  }
  return true;
}

void CloseRegion(EnvelopeEncryptionState& state, std::string_view line,
                 uint32_t line_num, const DelimiterMatch& delimiter,
                 std::string* transformed) {
  ReadIntoRegion(ExpressionsAheadOfDelimiter(line, delimiter), line_num,
                 &state.in_effect, &state.region);
  RegionEncryption how = RegionEncryptionFor(
      state.in_effect, state.region, state.exchange_key, state.keys, line_num);
  ReportClosedRegion(state.in_effect, how, state.keys, state.diag,
                     state.region.opened);
  transformed->append(
      ClosedRegionText(state.region, state.in_effect, line, delimiter, how));
  state.in_envelope = false;
  ReadOutsideRegion(ExpressionsBehindDelimiter(line, delimiter), line_num,
                    &state.in_effect);
}

void OpenRegion(EnvelopeEncryptionState& state, std::string_view line,
                SourceLoc loc, const DelimiterMatch& delimiter) {
  ReadOutsideRegion(ExpressionsAheadOfDelimiter(line, delimiter), loc.line,
                    &state.in_effect);
  state.in_envelope = true;
  state.region.opening_line = line;
  state.region.opened = loc;
  state.region.opening_directive =
      OpeningDirectiveOf(line, delimiter, kBeginDecryptionKeyword);
  state.region.source_body.clear();
  state.region.body.clear();
  state.region.written_inside = {};
  state.region.written_inside.encoding = state.in_effect.encoding;
  ReadIntoRegion(ExpressionsBehindDelimiter(line, delimiter), loc.line,
                 &state.in_effect, &state.region);
}

void EncryptLine(EnvelopeEncryptionState& state, std::string_view line,
                 SourceLoc loc, std::string* transformed) {
  if (CarriedAsComment(state, line, transformed)) return;
  if (SetAsideRejectedPragmaLine(line, loc, state.in_envelope, state.diag,
                                 transformed)) {
    return;
  }
  InputLine input =
      ReadInputLine(line, &state.previously_protected, state.diag, loc);
  DelimiterMatch delimiter = input.delimiter;
  if (state.in_envelope && delimiter.kind == EnvelopeDelimiter::kEnd) {
    CloseRegion(state, line, loc.line, delimiter, transformed);
    return;
  }
  if (!state.in_envelope && delimiter.kind == EnvelopeDelimiter::kBegin) {
    OpenRegion(state, line, loc, delimiter);
    return;
  }
  TakeKeyNamesOutsideProtectedBlock(line, loc.line, input.previously_protected,
                                    &state.in_effect);
  if (state.in_envelope) {
    ReportNestedRegion(delimiter, state.diag, loc);
    AppendEnvelopeLine(line, loc.line, input.previously_protected,
                       &state.region);
    return;
  }
  transformed->append(line);
}

}  // namespace

EnvelopeEncryptor::EnvelopeEncryptor(std::string_view exchange_key,
                                     const ProtectKeyList& keys,
                                     DiagEngine* diag)
    : state_(std::make_unique<EnvelopeEncryptionState>()) {
  state_->exchange_key = std::string(exchange_key);
  state_->keys = keys;
  state_->diag = diag;
}

EnvelopeEncryptor::~EnvelopeEncryptor() = default;

std::string EnvelopeEncryptor::Encrypt(std::string_view source_text,
                                       uint32_t file_id) {
  std::string transformed;
  uint32_t line_num = 0;
  for (std::string_view line : SplitLines(source_text)) {
    ++line_num;
    EncryptLine(*state_, line, LineOf(file_id, line_num), &transformed);
  }
  return transformed;
}

std::string EnvelopeEncryptor::Finish() {
  EnvelopeEncryptionState& state = *state_;
  if (!state.in_envelope) return {};
  state.in_envelope = false;
  std::string text(state.region.opening_line);
  text.append(state.region.source_body);
  return text;
}

std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key,
                             const ProtectKeyList& keys, DiagEngine* diag,
                             uint32_t file_id) {
  if (diag == nullptr && exchange_key.empty() && keys.Empty()) {
    return std::string(source_text);
  }
  EnvelopeEncryptor encryptor(exchange_key, keys, diag);
  std::string transformed = encryptor.Encrypt(source_text, file_id);
  transformed.append(encryptor.Finish());
  return transformed;
}

}  // namespace delta
