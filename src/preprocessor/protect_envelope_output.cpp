#include "preprocessor/protect_envelope_output.h"

#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

// The encoding pragma expression written ahead of one block of an envelope:
// the scheme the block is written under, and the size of the data those
// characters stand for.
//
// §34.5.9 has a count added by the encrypting tool for each block it writes,
// and lets an expression be written ahead of each block rather than once for
// the envelope, which is what a text stating a count per block needs. A count
// belongs to one block, so an envelope carrying two blocks writes two of
// these.
std::string BlockEncodingDirective(const ProtectEncoding& encoding,
                                   size_t bytes) {
  ProtectEncoding described = encoding;
  described.bytes = bytes;
  described.has_bytes = true;
  return ProtectEncodingDirective(described);
}

// §34.5.26 has the public key written into every protected block it was used
// for, followed by its encoded value, and §34.5.9 has that value encoded in
// the scheme the envelope declares. A key the source wrote under some other
// scheme is therefore written back out under this envelope's: the value
// carried across is the key, and the characters standing for it are whichever
// the reader of this envelope will be reading.
void AppendKeyPublicKey(std::string_view key, const ProtectEncoding& encoding,
                        std::string* text) {
  text->append(BlockEncodingDirective(encoding, key.size()));
  text->append(ProtectKeyPublicKeyDirective(EncodeProtectBlock(key, encoding)));
}

// The names and identifiers an envelope states in the clear.
//
// Each is written out because its own subclause makes an exception of it. The
// rest of what the enclosed text said goes into the block along with that text;
// these would leave a reader unable to learn what opens the block without
// opening it first, so they are lifted out and written ahead of the block they
// bear on. The order is the order §34.4 tabulates them in, each entity standing
// ahead of the designations read against it.
void AppendClearNames(const EncryptionEnvelope& envelope,
                      const ProtectEncoding& block_encoding,
                      std::string* text) {
  // §34.5.10 has the entity whose keys the data are under unchanged in what
  // the tool writes out, and §34.5.12 has the name of the key itself written
  // as cleartext. Lifting them out is what the standard's exceptions for these
  // two keywords are for; the exception the standard makes to the exception is
  // the digital envelope mechanism, which this implementation does not offer,
  // so both are always written in the clear. The entity comes first, the key
  // name being read against it.
  if (!envelope.names.data_keyowner.empty()) {
    text->append(ProtectDataKeyownerDirective(envelope.names.data_keyowner));
  }
  if (!envelope.names.data_keyname.empty()) {
    text->append(ProtectDataKeynameDirective(envelope.names.data_keyname));
  }
  // §34.5.18 makes the same exception for the name of the key the region's
  // digest is under. A region that named a key for its digest named one the
  // data's key name does not stand for, so leaving it in the block would put
  // the one name a reader needs for the digest out of reach behind the data.
  if (!envelope.names.digest_keyname.empty()) {
    text->append(ProtectDigestKeynameDirective(envelope.names.digest_keyname));
  }
  // §34.5.21 makes the same exception for the identifier naming the algorithm
  // the region's digests are computed with, and it is written ahead of the
  // block rather than after it: what the identifier is needed for is
  // recomputing a digest of that block, so a reader has to have it in hand by
  // the time the block is reached.
  if (!envelope.digest_method.empty()) {
    text->append(ProtectDigestMethodDirective(envelope.digest_method));
  }
  // §34.5.23 has the entity whose keys a region's own keys are under unchanged
  // in what the tool writes out, and makes no exception at all: the exception
  // the other two entities have is a key block, and this is the entity whose
  // key opens that block.
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

}  // namespace

ProtectEncoding EnvelopeBlockEncoding(const ProtectEncoding& requested) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  if (ProtectEncodingFitsPragmaValue(requested.enctype)) {
    encoding.enctype = requested.enctype;
  }
  return encoding;
}

std::string DecryptionEnvelopeText(const EncryptionEnvelope& envelope,
                                   const RegionEncryption& how) {
  std::string text;
  text.append(envelope.begin_directive);
  // The scheme the envelope's blocks are written under is stated for the
  // envelope as a whole, ahead of everything depending on it, and each block
  // restates it with the count of what that block holds.
  ProtectEncoding block_encoding =
      EnvelopeBlockEncoding(envelope.requested_encoding);
  std::string envelope_encoding = ProtectEncodingValue(block_encoding);
  text.append(ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, kDataMethod, envelope_encoding}));
  AppendClearNames(envelope, block_encoding, &text);
  // §34.5.27 has the blocks carrying the key the region's data are under
  // written into the envelope ahead of the block those keys open. A reader has
  // to hold the key before it reaches what the key is for, and there is nothing
  // else in the envelope that says what the data block is under: the key was
  // made for this region and travels nowhere but here.
  text.append(how.key_blocks.directives);
  // §34.5.9 has an encrypting tool state, against the bytes subkeyword, how
  // much data the block about to be written stands for. The count is of the
  // block before any of the encoding was applied to it, so it is taken from
  // what goes into the writing rather than from the characters that come out.
  text.append(BlockEncodingDirective(block_encoding,
                                     ProtectedRegionBlockSize(envelope.body)));
  text.append("`pragma protect ").append(kDataBlockKeyword).append("=\"");
  text.append(
      EncryptProtectedRegion(envelope.body, how.key, block_encoding.enctype));
  text.append("\"\n");
  text.append(envelope.end_directive);
  text.append(ProtectKeywordResetDirective());
  return text;
}

}  // namespace delta
