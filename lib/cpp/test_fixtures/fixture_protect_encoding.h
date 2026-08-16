#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// The regions, envelopes and encoded values a test about §34.5.9's coding
// scheme is written out of.
//
// An encoded value has no standing outside a protected envelope, so a test
// about the writing one is carried as states a region in real directive syntax,
// drives it through the encrypting half, and reads the envelope that comes
// back -- either by the published algorithm the region named, which is what
// says the tool wrote what it declared, or by the preprocessor, which is what
// says a reading takes the declaration back out. Everything below is one of
// those three: the values a region designates its keys by, the region syntax
// they are written in, and the places in a produced envelope a test reads.

// The key an IP author hands the encrypting half, and hands back to a tool
// reading what that half produced. Without one nothing is sealed and nothing is
// opened, so a reading that found no design text could not be told apart from a
// key that was never supplied.
inline constexpr std::string_view kExchangeKey = "globex-exchange-key";

// The design a region seals. Nothing of it survives any of the alphabets a
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
inline constexpr std::string_view kSealedDesign =
    "module sealed_m; endmodule\n";

// A second design, for the text that writes two regions. Two envelopes come
// back from such a text, and each has to describe itself: a rule about what
// every envelope carries is not observed by looking at one.
inline constexpr std::string_view kSecondDesign =
    "module sealed_n; endmodule\n";

// A design chosen to make the writing work for its living. It carries the one
// character that would end the value a block travels as, and a byte that cannot
// be printed at all, so a block recording it holds bytes no source line could
// carry until the writing has been applied.
//
// The unprintable byte is 0x02 rather than kKeywordMarker, which is 0x01. A
// source file may not hold that one: Preprocessor::ProcessSource reports it
// under §5.2 and blanks it, so that a keyword-version marker in preprocessed
// text is one the Preprocessor wrote. Text awaiting sealing is read by
// ProcessSource like any other, and the claim here is about a byte that cannot
// be printed, which 0x02 makes as well as 0x01 did.
inline constexpr std::string_view kAwkwardDesign =
    "module sealed_q; // \" \x02\nendmodule\n";

// Where a reading meets the block an envelope carries. Everything a block is
// read under has to stand ahead of this, so a directive written here is the
// last word on the writing in effect where the block is opened.
inline constexpr std::string_view kBlockOpening =
    "`pragma protect data_block=\"";

// §34.5.3.1's word, as the encrypting half writes it. It is where one envelope
// starts, so it is also how a text carrying two of them is cut in half.
inline constexpr std::string_view kProtectedOpening =
    "`pragma protect begin_protected";

// The keywords that speak for the line beneath them, each carrying one of the
// encoded values §34.5.9.2 lists. Reading a value means finding the line after
// one of these: §34.5.13's designation of the key the data are under,
// §34.5.26's designation of the key the region's own keys are under,
// §34.5.27's block carrying those keys, and §34.5.14's key inside it.
inline constexpr std::string_view kDataPublicKeyLine =
    "`pragma protect data_public_key\n";
inline constexpr std::string_view kKeyPublicKeyLine =
    "`pragma protect key_public_key\n";
inline constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";
inline constexpr std::string_view kDataDecryptKeyLine =
    "`pragma protect data_decrypt_key\n";

// The opening of any directive this subclause's keyword is written on.
inline constexpr std::string_view kAnyEncoding = "`pragma protect encoding=";

// §34.5.22's expression, which serves twice over in one text and is spelled the
// same way both times. Written between a region's delimiters it asks for a
// message digest, which is what makes an envelope carry a second block; written
// by the tool into the envelope it announces the digest on the line beneath it.
//
// A request travels into the block along with the design, so the only directive
// of this name left standing in the clear is the one the tool wrote.
inline constexpr std::string_view kDigestBlockLine =
    "`pragma protect digest_block\n";

// The entity that provided the key a region's own keys are under, as §34.5.23
// names it, and the key that entity holds.
inline constexpr std::string_view kKeyProvider = "acme";
inline constexpr std::string_view kProviderKey = "acme-provider-key";

// The public key a region designates that entity's key by, as §34.5.26 has it
// written: the keyword on one line and the key's encoded value on the next.
//
// It holds a space, the one character of it the four tabulated algorithms treat
// four different ways -- as itself, as an escape, as nothing recognizable, and
// as part of a group. A designation of letters alone would come out of raw and
// quoted-printable alike, and neither could then be told from the other.
inline constexpr std::string_view kDesignatedKey = "acme public";

// That same value written by each of the algorithms Table 34-2 names, spelled
// out here rather than produced by the tool under test: a designation this tool
// wrote for itself would be read back by whatever writing it happens to
// perform, while these are what the published algorithms produce. The identity
// transformation is not among them -- its row performs no writing, so the
// designation is the key and kDesignatedKey serves for both.
inline constexpr std::string_view kDesignationInBase64 = "YWNtZSBwdWJsaWM=";
inline constexpr std::string_view kDesignationInUuencode = "+86-M92!P=6)L:6,`";
inline constexpr std::string_view kDesignationInQuotedPrintable =
    "acme=20public";

// A designation holding a character that cannot be printed, for the one row of
// the table that admits such data. Written under any other scheme these bytes
// would be an escape or an alphabet member; written under this one they are the
// data.
//
// The byte is 0x02 rather than kKeywordMarker, for the reason given above
// kAwkwardDesign: this designation is written into a source line raw, and no
// source line may carry 0x01.
inline constexpr std::string_view kUnprintableDesignation = "acme\x02public";

// An identifier no row of Table 34-2 names and this implementation does not
// define either, so it stands for no writing at all.
inline constexpr std::string_view kUnprovidedEnctype = "x-nobody-provides-this";

// The directive this subclause defines, carrying `list` as the pragma_value
// written against the keyword.
inline std::string StatesEncoding(std::string_view list) {
  std::string directive(kAnyEncoding);
  directive.append(list).append("\n");
  return directive;
}

// The shortest value the keyword is defined with: the scheme alone, written as
// the string §34.5.9.1 calls for.
inline std::string NamesScheme(std::string_view enctype) {
  std::string list = "(enctype=\"";
  list.append(enctype).append("\")");
  return StatesEncoding(list);
}

// The text one region encloses: whatever it writes about itself, then the
// design it seals. The design comes last so that a line the encryption passed
// over is a line that went into the block ahead of it.
inline std::string RegionBody(std::string_view inside) {
  std::string body(inside);
  body.append(kSealedDesign);
  return body;
}

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with that body
// between them.
inline std::string RegionHolding(std::string_view inside) {
  std::string region = "`pragma protect begin\n";
  region.append(RegionBody(inside));
  region.append("`pragma protect end\n");
  return region;
}

// The expression an encrypting tool writes to state how much data one block
// stands for, as it stands in an envelope: the count against the bytes name,
// with the parenthesis that closes the list behind it. The parenthesis is part
// of what is looked for, a count of thirty-one being written by the same
// characters that begin a count of three hundred and ten.
inline std::string TheCountOf(size_t bytes) {
  std::string counted = "bytes=";
  counted.append(std::to_string(bytes)).append(")");
  return counted;
}

// What a reading is configured with for opening the protected regions an input
// carries, which is the key and nothing besides.
inline PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  return config;
}

// The envelope the encrypting half leaves where `source` wrote its regions,
// checked on the way out to be one: the design it was formed from is gone from
// the text.
//
// A round trip that looked only at what came back would pass on a region that
// was never sealed at all, the design being present in that text for the
// plainest of reasons and no block having been opened to put it there.
inline std::string EnvelopeOf(const std::string& source) {
  std::string envelope = EncryptEnvelopes(source, kExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign));
  return envelope;
}

// The envelope produced from one region writing `inside` between its
// delimiters.
inline std::string EnvelopeAround(std::string_view inside) {
  return EnvelopeOf(RegionHolding(inside));
}

// The characters recording one envelope's sealed region: what stands between
// the quotation marks of its data_block expression, and empty where the text
// carries no such expression.
inline std::string DataBlockOf(std::string_view envelope) {
  size_t opens = envelope.find(kBlockOpening);
  if (opens == std::string_view::npos) return {};
  size_t from = opens + kBlockOpening.size();
  size_t to = envelope.find('"', from);
  if (to == std::string_view::npos) return {};
  return std::string(envelope.substr(from, to - from));
}

// The part of `text` from where its first protected envelope opens. Text
// outside an envelope is carried across as the bytes it was written with, so a
// directive the source wrote ahead of a region is still standing in what comes
// back, and a search of the whole text would take it for the tool's.
inline std::string ProtectedPartOf(std::string_view text) {
  size_t opens = text.find(kProtectedOpening);
  if (opens == std::string_view::npos) return {};
  return std::string(text.substr(opens));
}

// The whole of the line standing after `opening`, which is where the keywords
// that speak for the line beneath them put their encoded value.
inline std::string LineAfter(std::string_view text, std::string_view opening) {
  size_t stands = text.find(opening);
  if (stands == std::string_view::npos) return {};
  size_t from = stands + opening.size();
  size_t to = text.find('\n', from);
  if (to == std::string_view::npos) return {};
  return std::string(text.substr(from, to - from));
}

// The same envelope with `directive` written into it immediately ahead of the
// expression carrying its block. §34.4 has a value in effect over the text
// after it, so a directive placed here is the one the block is read under
// whatever the envelope stated about itself further up.
inline std::string EnvelopeReadUnder(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t block = envelope.find(kBlockOpening);
  EXPECT_NE(block, std::string::npos);
  return envelope.insert(block, std::string(directive));
}

// The same envelope with `directive` written in at the other end of it, on the
// line after the word that opens the envelope. Everything the envelope says
// about itself, and everything each of its fields says, still stands after it.
inline std::string EnvelopeOpeningWith(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t opens = envelope.find(kProtectedOpening);
  EXPECT_NE(opens, std::string::npos);
  size_t ends = envelope.find('\n', opens);
  EXPECT_NE(ends, std::string::npos);
  return envelope.insert(ends + 1, std::string(directive));
}

// A text writing two regions one after the other, each sealing a design of its
// own.
inline std::string TwoRegions() {
  std::string source = "`pragma protect begin\n";
  source.append(kSealedDesign).append("`pragma protect end\n");
  source.append("`pragma protect begin\n");
  source.append(kSecondDesign).append("`pragma protect end\n");
  return source;
}

// A region designating the key its data are to be encrypted under by that key's
// encoded value, as §34.5.13 has such a designation written: the keyword
// standing alone and the value on the line beneath it, read under the writing
// the region names above it.
inline std::string RegionDesignatingTheDataKey(std::string_view enctype,
                                               std::string_view encoded) {
  std::string inside(NamesScheme(enctype));
  inside.append(kDataPublicKeyLine).append(encoded).append("\n");
  return RegionHolding(inside);
}

// A region that reaches no key by name and designates one instead, as §34.5.26
// has such a designation written: the entity that provided it, the writing the
// designation is spelled in, the keyword standing alone, and the encoded value
// on the line beneath it.
//
// The scheme is stated between the region's delimiters rather than ahead of
// them, so the line carrying the designation is read under a writing the region
// itself named.
inline std::string RegionDesignating(std::string_view enctype,
                                     std::string_view encoded) {
  std::string inside = "`pragma protect key_keyowner=\"";
  inside.append(kKeyProvider).append("\"\n");
  inside.append(NamesScheme(enctype));
  inside.append("`pragma protect key_public_key\n");
  inside.append(encoded).append("\n");
  return RegionHolding(inside);
}

// What the encrypting half leaves where that region was written, for a tool
// holding the provider's key under `held`.
//
// Nothing else can seal this region: it names no key of its own and the tool is
// handed no exchange key, so the only way to a key is the designation beneath
// the keyword, and reaching it means reading that line out of the writing the
// region named. A region left with its design in the clear reached nothing.
inline std::string SealedByDesignation(std::string_view enctype,
                                       std::string_view encoded,
                                       std::string_view held) {
  ProtectKeyList keys;
  keys.Add({std::string(kKeyProvider), std::string(held),
            std::string(kProviderKey)});
  return EncryptEnvelopes(RegionDesignating(enctype, encoded), "", keys);
}
