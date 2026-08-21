#include "preprocessor/protect_key_block.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

// The tabulated name of the keyword naming the cipher a region's data are
// under. It is spelled here because §34.5.27 forms a key block's buffer from
// that keyword and §34.5.14 has a reader find it inside one; the keyword's own
// definition is written elsewhere, and nothing here decides what it may say.

// One directive carrying one keyword and the string that keyword records.
void AppendDirective(std::string& text, std::string_view keyword,
                     std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=\"");
  text.append(value).append("\"\n");
}

// The single key one request designates, and an empty view where it designates
// none of the keys the tool holds.
//
// The public key is tried where the name reaches nothing rather than instead of
// it. §34.5.26 has a text writing both designate one key twice, so which is
// consulted first decides nothing; a request carrying only the second would be
// left designating nothing at all if the first were the only one tried.
std::string_view KeyOfRequest(const ProtectKeyBlockRequest& request,
                              const ProtectKeyList& keys) {
  std::string_view under_name = keys.KeyFor(request.keyowner, request.keyname);
  if (!under_name.empty()) return under_name;
  return keys.KeyFor(request.keyowner, request.public_key);
}

// The buffer one request's block is formed from: the data decryption pragma
// expressions §34.5.27 asks for, carrying the key made for this region, and
// beside them the digest decryption pragma expressions §34.5.20 stores in the
// same block.
//
// The cipher goes in whenever the region named one, that being where §34.5.17
// has the identifier written for every envelope carrying key blocks, and the
// algorithm the digests are computed under goes in on the same footing, that
// being where §34.5.21 has that identifier written for such an envelope. Both
// go in as the region stated them and neither goes in where the region stated
// nothing, a block filled from a default being a block claiming the author
// chose what this tool chose. The digest's key goes in only where a digest was
// asked for: a region generating no digest signs nothing, so a key written for
// a digest that is never produced would be a key nothing is ever opened with.
std::string KeyBlockContentFor(const ProtectKeyBlockRequest& request,
                               const ProtectKeyBlocks& blocks,
                               const ProtectDigestBlockPolicy& digest,
                               const ProtectEncoding& encoding) {
  ProtectDataDecryption data = request.data;
  data.decrypt_key = blocks.data_key;
  ProtectDigestDecryption digest_keys;
  digest_keys.key_method = digest.key_method;
  digest_keys.digest_method = digest.stated_method;
  if (digest.requested) digest_keys.decrypt_key = blocks.digest_key;
  return ProtectKeyBlockContent(data, digest_keys, encoding);
}

}  // namespace

std::string ProtectDataDecryptKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kDataDecryptKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

void ProtectKeyBlockRequests::Designate(std::string_view keyowner,
                                        std::string_view keyname,
                                        const ProtectDataDecryption& data,
                                        uint32_t line) {
  ProtectKeyBlockRequest request;
  request.keyowner = ProtectPragmaValueBody(keyowner);
  request.keyname = ProtectPragmaValueBody(keyname);
  request.data = data;
  request.line = line;
  requests_.push_back(std::move(request));
}

// The public key arrives as the key rather than as a pragma_value carrying one,
// the line that held it having already been read out of the scheme it was
// encoded under, so nothing is stripped from it.
void ProtectKeyBlockRequests::DesignatePublicKey(
    std::string_view keyowner, std::string_view key,
    const ProtectDataDecryption& data, uint32_t line) {
  ProtectKeyBlockRequest request;
  request.keyowner = ProtectPragmaValueBody(keyowner);
  request.public_key = key;
  request.data = data;
  request.line = line;
  requests_.push_back(std::move(request));
}

// The derivation is a message digest, which is the one computation in this
// implementation that turns a text of any length into a short value that no
// other text shares. A digest under an algorithm every tool provides is what
// the region and the key it will travel under are run through together, so the
// result depends on both and reveals neither.
std::string ProtectGeneratedDataKey(std::string_view cleartext,
                                    std::string_view under) {
  std::string material(under);
  material.append(cleartext);
  std::string key;
  if (!ProtectMessageDigest(material, kDefaultDigestMethod, &key)) return {};
  return key;
}

// The keyword naming the cipher comes first, because §34.5.14 has a reader take
// the cipher and the key out of the block together and neither opens anything
// without the other. The key comes last, on the line beneath the keyword
// carrying it, which is where §34.5.14 puts it.
std::string ProtectKeyBlockContent(const ProtectDataDecryption& data,
                                   const ProtectDigestDecryption& digest,
                                   const ProtectEncoding& encoding) {
  std::string text;
  AppendDirective(text, kDataMethodKeyword, data.method);
  // §34.5.9 governs this key as much as the block carrying it, and gives it a
  // count of its own. The expression has to be written here rather than left
  // to the one standing over the block, because that one describes the block:
  // a reader measuring this key against it would be holding the size of
  // everything the block contains against a key that is one part of it.
  text.append(ProtectEncodedValueDirective(encoding, data.decrypt_key.size()));
  text.append(ProtectDataDecryptKeyDirective(
      EncodeProtectBlock(data.decrypt_key, encoding)));
  // §34.5.20 stores the key that opens the region's digests in this same block,
  // and §34.5.17 has the cipher that key belongs to travel with it whenever a
  // digital signature is in use. They come after the data's own key because
  // that is the one a reader is here for: a reader that stopped at the data's
  // key has what it needs to reach the design.
  text.append(ProtectDigestDecryptionContent(digest, encoding));
  return text;
}

bool SameProtectDataDecryption(const ProtectDataDecryption& a,
                               const ProtectDataDecryption& b) {
  return a.method == b.method && a.keyname == b.keyname;
}

// §34.5.9 has an encrypting tool state, against the bytes subkeyword, how much
// data the block about to be written stands for, and a key block is one of the
// blocks that subclause governs. The count is of the buffer before any of the
// writing was applied to it, so it is taken from what goes into the encoding
// rather than from the characters that come out.
//
// The entity comes ahead of the designation read against it, and whichever
// designation the request carries is the one written: §34.5.26 makes the name
// and the public key alternatives, so a request that reached its key by the
// second is written with the second and a reader reaches the same key by the
// same route the writer took.
std::string ProtectKeyBlockDirectives(const ProtectKeyBlockRequest& request,
                                      std::string_view content,
                                      std::string_view key,
                                      const ProtectEncoding& encoding) {
  std::string text;
  AppendDirective(text, kKeyKeyownerKeyword, request.keyowner);
  if (!request.keyname.empty()) {
    AppendDirective(text, kKeyKeynameKeyword, request.keyname);
  } else {
    text.append(
        ProtectEncodedValueDirective(encoding, request.public_key.size()));
    text.append(ProtectKeyPublicKeyDirective(
        EncodeProtectBlock(request.public_key, encoding)));
  }
  text.append(ProtectEncodedValueDirective(encoding,
                                           ProtectedRegionBlockSize(content)));
  text.append("`pragma protect ").append(kKeyBlockKeyword).append("\n");
  text.append(EncryptProtectedRegion(content, key, encoding.enctype));
  text.push_back('\n');
  return text;
}

// One key is made for the region and every block carries that same key, which
// is what §34.5.27 requires of the blocks of a single envelope: they are
// alternative ways into one envelope, so a reader reaching any of them reaches
// the same data. It is made from the first key a request reached, so a region
// no request reached a key for gets none and is left untransformed.
//
// What may still differ between two of them is what the region wrote about the
// data between one designation and the next. Every request recorded the data
// decryption pragma expressions standing where it was made, so a region that
// changed one of them is one whose blocks do not all stand for the same account
// of the data, and each request after the first is measured against the first.
// The disagreement is reported beside the blocks rather than in place of them:
// the blocks are still what the region asked for, and what the condition costs
// is the report.
//
// It is the first request to disagree that is kept, one region drawing one
// report however many of its blocks differ from the first. A report per
// disagreeing block would say the same thing over again about one region, and
// the block an author has to look at to find what changed is the first one that
// stopped matching.
ProtectKeyBlocks ProtectKeyBlocksFor(const ProtectKeyBlockRequests& requests,
                                     std::string_view cleartext,
                                     const ProtectKeyList& keys,
                                     const ProtectEncoding& encoding,
                                     const ProtectDigestBlockPolicy& digest) {
  ProtectKeyBlocks blocks;
  const ProtectDataDecryption* first = nullptr;
  for (const ProtectKeyBlockRequest& request : requests.Requests()) {
    std::string_view key = KeyOfRequest(request, keys);
    if (key.empty()) continue;
    if (blocks.data_key.empty()) {
      blocks.data_key = ProtectGeneratedDataKey(cleartext, key);
      blocks.digest_key = ProtectGeneratedDigestKey(blocks.data_key);
    }
    if (first == nullptr) {
      first = &request.data;
    } else if (!SameProtectDataDecryption(*first, request.data) &&
               blocks.data_changed_line == 0) {
      blocks.data_changed_line = request.line;
    }
    std::string content = KeyBlockContentFor(request, blocks, digest, encoding);
    blocks.directives.append(
        ProtectKeyBlockDirectives(request, content, key, encoding));
    // §34.5.22 owes a digest block to each key block generated, immediately
    // following the block it refers to. The buffer the block was formed from is
    // what the digest is computed over, because that is what a reader holds
    // once it has opened the block and so what a reader recomputes the digest
    // from.
    ProtectDigestBlockPolicy block_digest = digest;
    block_digest.key = blocks.digest_key;
    blocks.directives.append(
        ProtectDigestBlockDirectives(content, block_digest, encoding));
  }
  return blocks;
}

}  // namespace delta
