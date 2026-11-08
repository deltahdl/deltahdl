#include "preprocessor/protect_envelope_output.h"

#include <string>
#include <string_view>

#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

void AppendKeyPublicKey(std::string_view key, const ProtectEncoding& encoding,
                        std::string* text) {
  text->append(ProtectEncodedValueDirective(encoding, key.size()));
  text->append(ProtectKeyPublicKeyDirective(EncodeProtectValue(key, encoding)));
}

void AppendDataPublicKey(std::string_view key, const ProtectEncoding& encoding,
                         std::string* text) {
  text->append(ProtectEncodedValueDirective(encoding, key.size()));
  text->append(
      ProtectDataPublicKeyDirective(EncodeProtectValue(key, encoding)));
}

void AppendDigestPublicKey(std::string_view key,
                           const ProtectEncoding& encoding, std::string* text) {
  text->append(ProtectEncodedValueDirective(encoding, key.size()));
  text->append(
      ProtectDigestPublicKeyDirective(EncodeProtectValue(key, encoding)));
}

void AppendClearDataNames(const EncryptionEnvelope& envelope,
                          const ProtectEncoding& one_line_encoding,
                          bool signed_envelope, std::string* text) {
  if (!signed_envelope && !envelope.names.data_keyowner.empty()) {
    text->append(ProtectDataKeyownerDirective(envelope.names.data_keyowner));
  }
  if (!signed_envelope && !envelope.names.data_keyname.empty()) {
    text->append(ProtectDataKeynameDirective(envelope.names.data_keyname));
  }
  if (!envelope.names.data_public_key.empty()) {
    AppendDataPublicKey(envelope.names.data_public_key, one_line_encoding,
                        text);
  }
}

void AppendClearDigestNames(const EncryptionEnvelope& envelope,
                            const ProtectEncoding& one_line_encoding,
                            bool signed_envelope, std::string* text) {
  if (!envelope.names.digest_keyowner.empty()) {
    text->append(
        ProtectDigestKeyownerDirective(envelope.names.digest_keyowner));
  }
  if (!signed_envelope && !envelope.digest_key_method.empty()) {
    text->append(ProtectDigestKeyMethodDirective(envelope.digest_key_method));
  }
  if (!signed_envelope && !envelope.names.digest_keyname.empty()) {
    text->append(ProtectDigestKeynameDirective(envelope.names.digest_keyname));
  }
  if (!envelope.names.digest_public_key.empty()) {
    AppendDigestPublicKey(envelope.names.digest_public_key, one_line_encoding,
                          text);
  }
  if (!signed_envelope && !envelope.digest_method.empty()) {
    text->append(ProtectDigestMethodDirective(envelope.digest_method));
  }
}

void AppendClearKeyNames(const EncryptionEnvelope& envelope,
                         const ProtectEncoding& one_line_encoding,
                         bool signed_envelope, std::string* text) {
  if (!envelope.names.key_keyowner.empty()) {
    text->append(ProtectKeyKeyownerDirective(envelope.names.key_keyowner));
  }
  if (signed_envelope) {
    std::string_view stated = ProtectPragmaValueBody(envelope.key_method);
    text->append("`pragma protect ").append(kKeyMethodKeyword).append("=\"");
    text->append(stated == kDesCbcMethod ? stated : kDataMethod);
    text->append("\"\n");
  }
  if (!envelope.names.key_keyname.empty()) {
    text->append(ProtectKeyKeynameDirective(envelope.names.key_keyname));
  }
  if (!envelope.names.key_public_key.empty()) {
    AppendKeyPublicKey(envelope.names.key_public_key, one_line_encoding, text);
  }
}

void AppendClearNames(const EncryptionEnvelope& envelope,
                      const ProtectEncoding& one_line_encoding,
                      bool signed_envelope, std::string* text) {
  AppendClearDataNames(envelope, one_line_encoding, signed_envelope, text);
  AppendClearDigestNames(envelope, one_line_encoding, signed_envelope, text);
  AppendClearKeyNames(envelope, one_line_encoding, signed_envelope, text);
}

}  // namespace

std::string_view RegionDigestKey(const RegionKeyNames& names,
                                 const ProtectKeyList& keys) {
  std::string_view owner = ProtectPragmaValueBody(names.digest_keyowner);
  if (owner.empty()) owner = ProtectPragmaValueBody(names.data_keyowner);
  std::string_view keyname = ProtectPragmaValueBody(names.digest_keyname);
  if (keyname.empty()) keyname = ProtectPragmaValueBody(names.data_keyname);
  std::string_view under_name = keys.KeyFor(owner, keyname);
  if (!under_name.empty()) return under_name;
  std::string_view public_key = names.digest_public_key;
  if (public_key.empty()) public_key = names.data_public_key;
  if (public_key.empty()) return {};
  return keys.KeyFor(owner, public_key);
}

ProtectEncoding EnvelopeBlockEncoding(const ProtectEncoding& requested) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  if (ProtectEncodingFitsOneLine(requested.enctype)) {
    encoding.enctype = requested.enctype;
  }
  encoding.line_length = requested.line_length;
  return encoding;
}

ProtectEncoding RequestedBlockEncoding(const ProtectEncoding& requested) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  if (ProtectEncodingIsAvailable(requested.enctype)) {
    encoding.enctype = requested.enctype;
  }
  encoding.line_length = requested.line_length;
  return encoding;
}

ProtectEnvelopeEncodings EnvelopeEncodings(const ProtectEncoding& requested) {
  return {RequestedBlockEncoding(requested), EnvelopeBlockEncoding(requested)};
}

std::string DecryptionEnvelopeText(const EncryptionEnvelope& envelope,
                                   const RegionEncryption& how) {
  std::string text;
  text.append(envelope.begin_directive);
  if (!envelope.author.empty()) {
    text.append(ProtectAuthorDirective(envelope.author));
  }
  if (!envelope.author_info.empty()) {
    text.append(ProtectAuthorInfoDirective(envelope.author_info));
  }
  ProtectEnvelopeEncodings encodings =
      EnvelopeEncodings(envelope.requested_encoding);
  std::string envelope_encoding = ProtectEncodingValue(encodings.one_line);
  const bool kSignedEnvelope = !how.key_blocks.directives.empty();
  std::string_view block_method = ProtectPragmaValueBody(envelope.data_method);
  if (block_method != kDesCbcMethod) block_method = kDataMethod;
  text.append(ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, kEncryptAgentInfo,
       kSignedEnvelope ? std::string_view{} : block_method,
       envelope_encoding}));
  AppendClearNames(envelope, encodings.one_line, kSignedEnvelope, &text);
  text.append(how.key_blocks.directives);
  text.append(ProtectEncodedValueDirective(
      encodings.blocks, ProtectedRegionBlockSize(envelope.body, block_method)));
  text.append(envelope.comment_directives);
  text.append("`pragma protect ").append(kDataBlockKeyword).append("\n");
  text.append(EncryptProtectedRegion(envelope.body, how.key,
                                     encodings.blocks.enctype, block_method,
                                     encodings.blocks.line_length));
  text.push_back('\n');
  text.append(ProtectDigestBlockDirectives(envelope.body, how.digest,
                                           encodings.blocks));
  text.append(envelope.end_directive);
  text.append(ProtectKeywordResetDirective());
  return text;
}

}  // namespace delta
