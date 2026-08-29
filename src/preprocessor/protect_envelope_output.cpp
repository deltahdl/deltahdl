#include "preprocessor/protect_envelope_output.h"

#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

// §34.5.26 has the public key written into every protected block it was used
// for, followed by its encoded value, and §34.5.9 has that value encoded in
// the scheme the envelope declares. A key the source wrote under some other
// scheme is therefore written back out under this envelope's: the value
// carried across is the key, and the characters standing for it are whichever
// the reader of this envelope will be reading.
void AppendKeyPublicKey(std::string_view key, const ProtectEncoding& encoding,
                        std::string* text) {
  text->append(ProtectEncodedValueDirective(encoding, key.size()));
  text->append(ProtectKeyPublicKeyDirective(EncodeProtectBlock(key, encoding)));
}

// §34.5.13 says the same of the public key a region's data are under: the
// keyword goes into each protected block the designation was used for, followed
// by that key's encoded value, and §34.5.9 has the value written in the scheme
// the envelope declares. A key the source wrote under some other scheme is
// therefore written back out under this envelope's, the value carried across
// being the key rather than the characters that spelled it.
void AppendDataPublicKey(std::string_view key, const ProtectEncoding& encoding,
                         std::string* text) {
  text->append(ProtectEncodedValueDirective(encoding, key.size()));
  text->append(
      ProtectDataPublicKeyDirective(EncodeProtectBlock(key, encoding)));
}

// §34.5.19 says the same of the public key a region's digest is under: the
// keyword goes into each protected block the designation was used for, followed
// by that key's encoded value, and §34.5.9 has the value written in the scheme
// the envelope declares. A key the source wrote under some other scheme is
// therefore written back out under this envelope's, the value carried across
// being the key rather than the characters that spelled it.
void AppendDigestPublicKey(std::string_view key,
                           const ProtectEncoding& encoding, std::string* text) {
  text->append(ProtectEncodedValueDirective(encoding, key.size()));
  text->append(
      ProtectDigestPublicKeyDirective(EncodeProtectBlock(key, encoding)));
}

// The names and identifiers an envelope states in the clear.
//
// Each is written out because its own subclause makes an exception of it. The
// rest of what the enclosed text said goes into the block along with that text;
// these would leave a reader unable to learn what opens the block without
// opening it first, so they are lifted out and written ahead of the block they
// bear on. The order is the order §34.4 tabulates them in, each entity standing
// ahead of the designations read against it.
//
// `signed_envelope` says the envelope carries the region's keys in key blocks
// of its own. §34.5.27.2 has an encrypting tool form a key block when it is
// requested to use a digital signature, so an envelope carrying one is an
// envelope a digital signature was requested for -- and a digital signature is
// the exception several of these subclauses make to the exception that lifted
// the name out here. What one of them lifts out, the other puts inside the
// block instead.
//
// The three groups below are the three keys §34.5 writes names for: the key a
// region's data are under, the key its digest is under, and the key its own
// keys are under. A designation is read against the entity written beside it,
// so a name of one group reaches no key of another.

// The designations §34.5.10 through §34.5.13 write for the key a region's data
// are under.
void AppendClearDataNames(const EncryptionEnvelope& envelope,
                          const ProtectEncoding& block_encoding,
                          bool signed_envelope, std::string* text) {
  // §34.5.10.2 has the entity whose keys the data are under unchanged in the
  // output file, except where a digital signature is used, in which case it is
  // encrypted with the key_method and placed in a key_block. An envelope
  // carrying key blocks writes the entity into those blocks, and one without
  // them writes it here. It stands ahead of the designation read against it in
  // either place.
  if (!signed_envelope && !envelope.names.data_keyowner.empty()) {
    text->append(ProtectDataKeyownerDirective(envelope.names.data_keyowner));
  }
  // §34.5.12.2 has the name of the key itself output as cleartext in the output
  // file except where a digital envelope is used, and for a digital envelope
  // mechanism it is encrypted using the key_method and the key_keyname or
  // key_public_key and encoded in the key_block. An envelope carrying key
  // blocks writes the name into them, and one without them writes it here.
  if (!signed_envelope && !envelope.names.data_keyname.empty()) {
    text->append(ProtectDataKeynameDirective(envelope.names.data_keyname));
  }
  // §34.5.13 has the other designation of that same key written into every
  // protected block it was used for, with its encoded value beneath it, and
  // makes no exception for a digital signature the way the two names above do.
  // A region that designated its key this way is opened through this value, so
  // an envelope that kept it inside the block would be one nothing could pick
  // the key for.
  if (!envelope.names.data_public_key.empty()) {
    AppendDataPublicKey(envelope.names.data_public_key, block_encoding, text);
  }
}

// The designations §34.5.16 through §34.5.19 write for the key a region's
// digest is under, with the identifier §34.5.17 names the cipher for that key
// by and the identifier §34.5.21 names the algorithm computing the digest by.
void AppendClearDigestNames(const EncryptionEnvelope& envelope,
                            const ProtectEncoding& block_encoding,
                            bool signed_envelope, std::string* text) {
  // §34.5.16.2 has the entity whose key a region's digest is under unchanged in
  // the output file, except where a digital signature is used, in which case it
  // is encrypted with the digest_key_method and placed in a digest_key_block.
  //
  // The name is written here whether the envelope carries key blocks or not,
  // because the standard defines no digest_key_block. §34.4 states that "this
  // standard defines the pragma keyword names listed in Table 34-1 for use with
  // the protect pragma", Table 34-1 lists key_block and no digest_key_block,
  // and §34.5 runs from §34.5.1 to §34.5.32 without a subclause for one, so the
  // construct has neither a syntax nor a description. §34.5.1.2 enumerates the
  // blocks an envelope holds as "the data_block and key_block pragma
  // expressions" and names no third. A tool writing a digest_key_block would be
  // writing a directive whose keyword §34.4 does not admit, and no reader could
  // be required to open it, so the sentence's exception has no destination and
  // its main clause is the whole of what a conforming tool can act on.
  //
  // The neighbouring subclauses send their values into the key_block instead,
  // which is why this one stands alone: §34.5.17.2 has the digest_key_method
  // "encrypted with the key_method algorithm" and using "the key found in the
  // key_block", and §34.5.18.2 has the digest_keyname "encoded in the
  // key_block". §34.5.16.2 is the only one naming a digest_key_method cipher
  // and a digest_key_block destination. Issue #3429 settled this reading.
  //
  // It stands ahead of the designations read against it, the way each entity
  // does, since a name read against the wrong list picks out a key of somebody
  // else.
  if (!envelope.names.digest_keyowner.empty()) {
    text->append(
        ProtectDigestKeyownerDirective(envelope.names.digest_keyowner));
  }
  // §34.5.17.2 has the identifier naming the cipher a region's digests are
  // encrypted under unchanged in the output file, except where a digital
  // signature is used, in which case it is encrypted with the key_method
  // algorithm and uses the key found in the key_block. A region carrying key
  // blocks has one, and its identifier is written into the block instead; a
  // region without one states it here, since a reader has to know what a digest
  // is under before it can check the block that digest vouches for.
  if (!signed_envelope && !envelope.digest_key_method.empty()) {
    text->append(ProtectDigestKeyMethodDirective(envelope.digest_key_method));
  }
  // §34.5.18.2 has the name of the key the region's digest is under output as
  // cleartext in the output file except where a digital envelope is used, and
  // for a digital envelope mechanism it is encrypted using the key_method and
  // the key_keyname or key_public_key and encoded in the key_block. An envelope
  // carrying key blocks writes the name into them, and one without them writes
  // it here. The entity the name is read against stands in the clear either
  // way, §34.5.16.2 sending that entity to a block this implementation does not
  // write.
  if (!signed_envelope && !envelope.names.digest_keyname.empty()) {
    text->append(ProtectDigestKeynameDirective(envelope.names.digest_keyname));
  }
  // §34.5.19 has the other designation of that same key written into every
  // protected block it was used for, with its encoded value beneath it, and
  // states no exception for a digital signature the way the names above do. A
  // region that designated its digest's key this way has its digest opened
  // through this value, so an envelope that kept it inside the block would put
  // the designation behind the very block the digest vouches for -- and one
  // that wrote no name for its digest's key has nothing to fall back on.
  if (!envelope.names.digest_public_key.empty()) {
    AppendDigestPublicKey(envelope.names.digest_public_key, block_encoding,
                          text);
  }
  // §34.5.21.2 has the identifier naming the algorithm the region's digests are
  // computed with unchanged in the output file, except where a digital
  // signature is used, in which case it is encrypted with the key_method and
  // placed in a key_block. A region carrying key blocks has one, and its
  // identifier is written into the block instead. A region without them states
  // it here, ahead of the blocks rather than after them, because what the
  // identifier is needed for is recomputing a digest of a block: a reader has
  // to have it in hand by the time the block is reached, and a key block puts
  // it in hand a line sooner than that.
  if (!signed_envelope && !envelope.digest_method.empty()) {
    text->append(ProtectDigestMethodDirective(envelope.digest_method));
  }
}

// The designations §34.5.23 through §34.5.26 write for the key a region's own
// keys are under, with the identifier §34.5.24 names the cipher for that key
// by. None of them is lifted into a key block: this is the entity whose key
// opens that block, and what a reader combines with it to reach that key.
void AppendClearKeyNames(const EncryptionEnvelope& envelope,
                         const ProtectEncoding& block_encoding,
                         std::string* text) {
  // §34.5.23 has the entity whose keys a region's own keys are under unchanged
  // in what the tool writes out, and makes no exception at all: §34.5.10.2
  // sends the entity named for the data into a key_block, and this is the
  // entity whose key opens that block.
  if (!envelope.names.key_keyowner.empty()) {
    text->append(ProtectKeyKeyownerDirective(envelope.names.key_keyowner));
  }
  // §34.5.24 has the identifier naming the algorithm a region's own keys are
  // encrypted under unchanged in the output file, and it is written ahead of
  // the blocks rather than after them: what the identifier is needed for is
  // opening the block those keys are held in, so a reader has to have it in
  // hand by the time a block is reached.
  if (!envelope.key_method.empty()) {
    text->append(ProtectKeyMethodDirective(envelope.key_method));
  }
  // §34.5.25 has the name of the key a region's own keys are under written as
  // cleartext as well. It is the name a reader combines with the entity beside
  // it to reach the key the region is opened through, so leaving it among the
  // lines about to become unreadable would put the way in behind the door it
  // unlocks.
  if (!envelope.names.key_keyname.empty()) {
    text->append(ProtectKeyKeynameDirective(envelope.names.key_keyname));
  }
  // §34.5.26 has the other designation of that key written into every
  // protected block it was used for, with its encoded value beneath it. A
  // region that designated its key this way is opened through this value, so
  // an envelope that kept it inside the block would be one nothing could pick
  // the key for -- and the region designated no key by name to fall back on.
  if (!envelope.names.key_public_key.empty()) {
    AppendKeyPublicKey(envelope.names.key_public_key, block_encoding, text);
  }
}

void AppendClearNames(const EncryptionEnvelope& envelope,
                      const ProtectEncoding& block_encoding,
                      bool signed_envelope, std::string* text) {
  AppendClearDataNames(envelope, block_encoding, signed_envelope, text);
  AppendClearDigestNames(envelope, block_encoding, signed_envelope, text);
  AppendClearKeyNames(envelope, block_encoding, text);
}

}  // namespace

// Both halves are read off what the region left standing rather than off any
// one directive, the scope of these names being lexical: the values in effect
// where a region closes are the ones that region's digest belongs to.
//
// What decides whether a half was filled in is the value written rather than
// the expression carrying it, so an expression carrying nothing sends the
// reading to the other name exactly as leaving the expression out does. A
// reader pairs the two names on those terms, and a writer pairing them on any
// other would seal a digest under one key while the envelope sends its reader
// to another.
std::string_view RegionDigestKey(const RegionKeyNames& names,
                                 const ProtectKeyList& keys) {
  std::string_view owner = ProtectPragmaValueBody(names.digest_keyowner);
  if (owner.empty()) owner = ProtectPragmaValueBody(names.data_keyowner);
  std::string_view keyname = ProtectPragmaValueBody(names.digest_keyname);
  if (keyname.empty()) keyname = ProtectPragmaValueBody(names.data_keyname);
  std::string_view under_name = keys.KeyFor(owner, keyname);
  if (!under_name.empty()) return under_name;
  // §34.5.19's designation, taken the same way: the public key the region wrote
  // for its digest, or the one its data carry where the digest wrote none. A
  // region that designated neither has nothing here to read against the entity,
  // and asking first is what tells that region apart from one whose designation
  // reaches none of the keys held -- an empty designation would otherwise
  // select whichever key that entity happened to hold under an empty name.
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
  return encoding;
}

std::string DecryptionEnvelopeText(const EncryptionEnvelope& envelope,
                                   const RegionEncryption& how) {
  std::string text;
  text.append(envelope.begin_directive);
  // §34.5.5 has the name of whoever wrote the design placed in a directive the
  // envelope encloses. It stands ahead of everything describing the encryption,
  // which is the order §34.4 tabulates the keywords in, and it stands in the
  // clear: a reader holding no key at all still learns whose design this is.
  if (!envelope.author.empty()) {
    text.append(ProtectAuthorDirective(envelope.author));
  }
  // §34.5.6 has whatever further the author offered about themselves placed in
  // a directive the envelope encloses as well. It follows the name, that being
  // the order §34.4 tabulates the two in, and it stands in the clear for the
  // reason the name does: a reader holding no key at all still learns what the
  // author of this design had to say about it.
  if (!envelope.author_info.empty()) {
    text.append(ProtectAuthorInfoDirective(envelope.author_info));
  }
  // The scheme the envelope's blocks are written under is stated for the
  // envelope as a whole, ahead of everything depending on it, and each block
  // restates it with the count of what that block holds.
  ProtectEncoding block_encoding =
      EnvelopeBlockEncoding(envelope.requested_encoding);
  std::string envelope_encoding = ProtectEncodingValue(block_encoding);
  const bool kSignedEnvelope = !how.key_blocks.directives.empty();
  // §34.5.11.2 sends the cipher the region's data are under into the key_block
  // where a digital signature is used, which is what an envelope carrying key
  // blocks is. The description then states no cipher and
  // ProtectEnvelopeDescriptionDirectives writes none.
  text.append(ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, kEncryptAgentInfo,
       kSignedEnvelope ? std::string_view{} : kDataMethod, envelope_encoding}));
  AppendClearNames(envelope, block_encoding, kSignedEnvelope, &text);
  // §34.5.27 has the blocks carrying the key the region's data are under
  // written into the envelope ahead of the block those keys open. A reader has
  // to hold the key before it reaches what the key is for, and there is nothing
  // else in the envelope that says what the data block is under: the key was
  // made for this region and travels nowhere but here.
  text.append(how.key_blocks.directives);
  // §34.5.30 has the entire comment including the beginning pragma output in
  // cleartext immediately prior to the data block of the begin-end it was found
  // in. It is written here, after everything else describing the envelope,
  // because the one expression it may not be separated from the block by is the
  // count on the line below: §34.5.9 states that count against the block it
  // counts, so the comment stands ahead of the count rather than between the
  // two.
  text.append(envelope.comment_directives);
  // §34.5.9 has an encrypting tool state, against the bytes subkeyword, how
  // much data the block about to be written stands for. The count is of the
  // block before any of the encoding was applied to it, so it is taken from
  // what goes into the writing rather than from the characters that come out.
  text.append(ProtectEncodedValueDirective(
      block_encoding, ProtectedRegionBlockSize(envelope.body)));
  // §34.5.15.1 spells the expression as the keyword standing alone, and
  // §34.5.15.2 has it indicate "that a data block begins on the next line in
  // the file". The block is therefore written beneath the keyword rather than
  // against it, which is where §34.5.22.1 and §34.5.27.1 already put the digest
  // block and the key block: ProtectDigestBlockDirectives
  // (preprocessor/protect_digest_block.cpp) and ProtectKeyBlockDirective
  // (preprocessor/protect_key_block.cpp) are the same three lines.
  text.append("`pragma protect ").append(kDataBlockKeyword).append("\n");
  text.append(
      EncryptProtectedRegion(envelope.body, how.key, block_encoding.enctype));
  text.push_back('\n');
  // §34.5.22 owes a digest block to the data block as well as each key block,
  // immediately following the block it refers to. The digest is computed over
  // the region's own text, that being what a reader holds once it has opened
  // the block and so what a reader recomputes the digest from.
  text.append(
      ProtectDigestBlockDirectives(envelope.body, how.digest, block_encoding));
  text.append(envelope.end_directive);
  text.append(ProtectKeywordResetDirective());
  return text;
}

}  // namespace delta
