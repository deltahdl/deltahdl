#include "preprocessor/protect_digest_key.h"

#include <string>
#include <string_view>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

// The tabulated name of the keyword naming the cipher a region's data are
// under. It is spelled here because §34.5.17 settles its own default by sending
// the reader to that keyword; the keyword's own definition is written
// elsewhere, and nothing here decides what it may say.

// What the derivation of a digest's key is run over along with the key the data
// are under, so that the two keys differ. Without it the derivation of one key
// from the other would have to be an identity, and a digest encrypted under the
// key its data are under is opened by everyone the data are.
constexpr std::string_view kDigestKeyDerivationMarker = "digest-key:";

// One directive carrying one keyword and the value it records, spelled as the
// source spelled it.
//
// §22.5.1 gives a pragma_value more than one spelling, and a keyword recording
// a string is not thereby barred from being written with an identifier or a
// number against it. Settling on one spelling would leave a value spelled
// another way rewritten -- a name written bare coming back in quotes -- which
// is a change to the very thing a keyword required to be unchanged may not
// undergo.
void AppendDirectiveAsWritten(std::string& text, std::string_view keyword,
                              std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=");
  text.append(value).append("\n");
}

}  // namespace

// The values are the ones the other method keyword admits, that being the whole
// of what §34.5.17 says about which values it takes: it sends a reader to that
// keyword's table and adds nothing to it.
bool IsProtectDigestKeyMethodIdentifier(std::string_view identifier) {
  return IsProtectKeyMethodIdentifier(identifier);
}

// A directive that wrote the keyword with nothing against it named no cipher
// any more than leaving the keyword out did, so the default fills the place in
// both cases and is reported as a default in both.
//
// What fills it is the cipher in effect for the region's data. A region that
// named none for either is left with none here as well, which is a different
// state from naming one: there is nothing to open a digest with rather than a
// cipher the region chose.
ProtectKeywordValue ProtectDigestKeyMethodInEffect(
    const ProtectKeywordScope& scope) {
  ProtectKeywordValue written = scope.ValueOf(kDigestKeyMethodKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {scope.ValueOf(kDataMethodKeyword).value, true};
}

std::string ProtectDigestKeyMethodDirective(std::string_view method) {
  std::string text;
  AppendDirectiveAsWritten(text, kDigestKeyMethodKeyword, method);
  return text;
}

// The keyword stands alone on its line and the key follows on the next, which
// is the shape §34.5.20 defines it in. Written against the keyword, the key
// would be a pragma_value of the directive, and a reader looking where the
// standard says to look would find the line beneath it holding something else.
//
// The whole of that line is the value, so the line goes out carrying what it
// carried. Nothing about it is a pragma_value, and treating it as one would let
// an encoded key that happens to begin and end with a quotation mark come back
// two characters shorter than the key it encodes.
std::string ProtectDigestDecryptKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kDigestDecryptKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

// The keyword naming the cipher comes first, because §34.5.20 has a reader take
// the cipher and the key out of the block together and neither opens anything
// without the other. The name of the key follows the cipher, that being the
// order §34.4 tabulates the two in. The key comes last, on the line beneath the
// keyword carrying it, which is where §34.5.20 puts it.
//
// A region naming no cipher for its digests writes none here. §34.5.17 fills
// that place from the cipher the region's data are under, which the envelope
// states in the clear already, so a copy sealed inside the block would tell a
// reader nothing it could not read without the key.
//
// A region generating no digest writes no key. The cipher still goes in, that
// being where §34.5.17 has it written whenever a digital signature is used, but
// a key made for a digest that is never produced would open nothing.
std::string ProtectDigestDecryptionContent(
    const ProtectDigestDecryption& digest, const ProtectEncoding& encoding) {
  std::string text;
  if (!digest.key_method.empty()) {
    AppendDirectiveAsWritten(text, kDigestKeyMethodKeyword, digest.key_method);
  }
  // §34.5.18.2 has the name of the key a region's digests are under encoded in
  // this block wherever a digital envelope mechanism is used, rather than
  // written in the clear beside it. A region that named no key for its digests
  // writes none here: §34.5.18 fills that place from the name the region's data
  // are under, and a name this tool put there would be a key the author never
  // designated.
  if (!digest.keyname.empty()) {
    text.append(ProtectDigestKeynameDirective(digest.keyname));
  }
  // §34.5.21 has the algorithm a region's digests were computed under written
  // into this block wherever a digital signature is used, rather than in the
  // clear beside it. It follows the cipher because that is the order §34.4
  // tabulates the two names in, and it is written as the source wrote it
  // because §34.5.21 has the identifier unchanged wherever it goes out.
  if (!digest.digest_method.empty()) {
    AppendDirectiveAsWritten(text, kDigestMethodKeyword, digest.digest_method);
  }
  if (!digest.decrypt_key.empty()) {
    // §34.5.9 gives this key a count of its own, and it has to be written here
    // rather than left to the expression standing over the block that carries
    // it: that one states the size of the whole block, and a reader measuring
    // this key against it would be holding one part against the size of all.
    text.append(
        ProtectEncodedValueDirective(encoding, digest.decrypt_key.size()));
    text.append(ProtectDigestDecryptKeyDirective(
        EncodeProtectBlock(digest.decrypt_key, encoding)));
  }
  return text;
}

// The derivation is a message digest, which is the one computation in this
// implementation that turns a text of any length into a short value that no
// other text shares. Running the data's key through it under a marker of this
// derivation's own is what puts the digest under a key of its own: the result
// depends on the data's key and reveals it no more than a digest reveals the
// text it was computed from.
std::string ProtectGeneratedDigestKey(std::string_view data_key) {
  if (data_key.empty()) return {};
  std::string material(kDigestKeyDerivationMarker);
  material.append(data_key);
  std::string key;
  if (!ProtectMessageDigest(material, kDefaultDigestMethod, &key)) return {};
  return key;
}

}  // namespace delta
