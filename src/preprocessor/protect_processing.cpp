#include "preprocessor/protect_processing.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_input_line.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"
#include "preprocessor/protect_region_lines.h"

namespace delta {
namespace {

// How a region's cleartext becomes the bytes a block records, and those bytes
// the cleartext again, is written in protect_processing_cipher.cpp. What one
// line of a source text says -- which protect pragma keywords it names, and how
// -- is answered in protect_pragma_line.cpp. Where one line of an encrypting
// tool's input stands, and what §34.5 makes an error in it, is answered in
// protect_input_line.cpp. What one line of an encryption envelope says about
// the keys the region it delimits is under is read in
// protect_region_lines.cpp. What the envelope taking a region's place says is
// written in protect_envelope_output.cpp. What this file does is find the
// regions a source text delimits and encrypt each one under the key standing
// where it closes; the other five are reached through the declarations they
// share.

// The report a region asking to be encrypted under a cipher this implementation
// does not provide is owed.
//
// §34.5.11.2 has the identifier name "the encryption algorithm that shall be
// used to encrypt subsequent begin-end blocks", so a region naming one has
// stated what its blocks are to be produced with. This implementation provides
// one cipher and names it kDataMethod (preprocessor/protect_envelope_output.h),
// and encrypting a region under that where the text named another would hand
// the author a file claiming an algorithm nobody used.
//
// The report says which half of Table 34-3 the identifier came from. One the
// table marks required is "standard in every implementation", so a text naming
// it assumed nothing and this tool is what falls short; #3430 covers providing
// those ciphers. Any other names a cipher a text assumed its reader knew.
//
// A region naming nothing is not refused anything, and neither is one naming
// the identifier this tool writes.
void ReportUnprovidedDataMethod(const RegionKeyReader& in_effect,
                                DiagEngine* diag, uint32_t file_id) {
  if (diag == nullptr) return;
  std::string_view stated = ProtectPragmaValueBody(in_effect.data_method);
  if (stated.empty() || stated == kDataMethod) return;
  std::string message(
      "protect pragma data_method asks for an encryption algorithm this "
      "implementation does not provide: ");
  message.append(stated);
  message.append(IsRequiredProtectEncryptionAlgorithm(stated)
                     ? ", which IEEE 1800-2023 Table 34-3 requires of every "
                       "implementation"
                     : ", which IEEE 1800-2023 Table 34-3 does not require of "
                       "every implementation");
  diag->Error(LineOf(file_id, in_effect.data_method_line), message,
              Subclause("34.5.11.2"));
}

// One encryption envelope as it is read, line by line: the directive that
// opened it in both spellings needed -- as the source wrote it, and as the
// envelope taking its place will carry it -- the text read since, and what
// that text said about the key its own data are under.
struct ReadRegion {
  std::string_view opening_line;
  std::string opening_directive;
  // Every line the region enclosed, as the source wrote it. A region there is
  // nothing to encrypt goes back exactly as it stands, so what goes back is
  // this rather than what a block would have recorded.
  std::string source_body;
  // The part of that text a block records. §34.5.5 keeps the author's name out
  // of it, §34.5.6 keeps out whatever further that author offered and §34.5.30
  // keeps out the documentation the region wrote for nothing to interpret, all
  // three being written in the clear inside the envelope instead, so a
  // directive carrying any of them is held back from here.
  std::string body;
  RegionKeyReader written_inside;
};

// Whether one line of an encryption envelope's enclosed text carries one of the
// three expressions the envelope publishes in the clear rather than encrypting:
// the one §34.5.5 names the design's author with, the one §34.5.6 offers
// anything further about them on, and the one §34.5.30 carries documentation
// nothing goes on to interpret on.
//
// §34.5.30.2 states outright what a line lifted out is spared, and it is the
// reason all three are lifted: text swept into the block is unreadable until
// somebody holds the key, and a copyright notice is exactly the thing an author
// writes to be read by whoever cannot. It gives a second reason of its own --
// such a value is known cleartext inside the block, which is what a
// known-plaintext attack is mounted from.
//
// It is the spelling §34.5.5.1, §34.5.6.1 and §34.5.30.1 define that counts:
// the keyword with a string written against it. Any of the three standing alone
// carries nothing, and so does any of them carrying a parenthesized list of
// further expressions, a list being something other than the one written thing
// a string is. No subclause says anything about those spellings, so §34.5.1's
// rule for everything else between the delimiters is what governs -- the line
// goes into the block along with the rest.
//
// The two questions this file asks about each expression -- whether the line
// carries it, and what it says -- are asked of the same spelling, so a line
// held back from the block is a line whose value the envelope goes on to carry.
// Were one of them to admit a spelling the other turned away, a line would be
// kept out of the block on account of a value that never reached the envelope,
// and the design would lose it in both directions at once.
//
// A line a previously generated protected block contains carries nothing of the
// kind either. §34.5.3 leaves the expressions of such a line uninterpreted and
// §34.5.1 has that block travel into the larger envelope as the bytes it is
// written with, so an expression written there describes a design some earlier
// encryption sealed rather than this one.
bool LiftedIntoTheClear(std::string_view line, bool previously_protected) {
  if (previously_protected) return false;
  return !KeywordSingleValueOnLine(line, kAuthorKeyword).empty() ||
         !KeywordSingleValueOnLine(line, kAuthorInfoKeyword).empty() ||
         !KeywordSingleValueOnLine(line, kCommentKeyword).empty();
}

// Adds one line of enclosed text to the region being read: to the text that
// goes back where the region cannot be encrypted, to the text a block records
// unless §34.5.5, §34.5.6 or §34.5.30 holds it back from there, and to what the
// region has said about itself.
void AppendEnvelopeLine(std::string_view line, uint32_t line_num,
                        bool previously_protected, ReadRegion* region) {
  region->source_body.append(line);
  if (!LiftedIntoTheClear(line, previously_protected)) {
    region->body.append(line);
  }
  // What the region itself wrote is kept apart from what is merely in effect
  // over it: those are the expressions the envelope has to carry in the clear,
  // the rest of the region's text being about to stop being readable. One
  // written outside the region is in the output already.
  TakeKeyNamesOutsideProtectedBlock(line, line_num, previously_protected,
                                    &region->written_inside);
}

// The key one region's data are encrypted under. §34.5.10 has the entity a
// region names select it out of the keys supplied under the names that select
// them, so two regions naming two entities are encrypted under two keys.
//
// A user who supplied keys under no names at all supplied one key for every
// region, whoever a region names, and that key is what every region is
// encrypted under. That is the whole of what a user holding one key needs to
// say, which is why it is not the same thing as a list holding one entry.
//
// The names a region writes for its own keys reach no key here. §34.5.27 has
// those name the key a key block is encrypted under, and a region carrying one
// has asked for the arrangement below, in which the block its data are under is
// under a key of the tool's own making instead. Reading them here as well would
// leave the region encrypted under the key that opens its key block, which is
// the one key that block was written to keep out of the clear.
// §34.5.13 gives the region a second way to pick that key out: the public key
// it is, written beneath the keyword announcing it rather than against a name.
// It is an alternative to the name given to the key rather than a companion of
// it -- a region writing both has picked out one key twice -- so it is tried
// where the name reaches nothing rather than instead of the name, and a region
// writing only this one designates its key as fully as one writing only the
// other.
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

// The key block a region asks for by what stands in effect over it rather than
// by what it writes between its own delimiters.
//
// §34.4 makes the scope of a designation lexical, so one written ahead of a
// region designates a key for that region as much as one written inside it, and
// a region that wrote none of its own has not thereby asked for nothing. It is
// consulted only where the region wrote none, because a region that did write
// its own said which readers this envelope is for.
//
// `closing_line` is the 1-based line the region's closing expression stands on,
// and it is what the one request this can produce records. The designation
// itself was written ahead of the region, where it stood for whichever region
// closed next rather than for this one, so where it asks for a block is where
// this region ends. Nothing reads the line off a lone request either way:
// §34.5.27's requirement is one two blocks can break and one cannot.
ProtectKeyBlockRequests DesignatedKeyBlocks(const RegionKeyNames& names,
                                            uint32_t closing_line) {
  ProtectKeyBlockRequests requests;
  if (!names.key_keyname.empty()) {
    requests.Designate(names.key_keyowner, names.key_keyname,
                       DataDecryptionInEffect(names), closing_line);
  } else if (!names.key_public_key.empty()) {
    requests.DesignatePublicKey(names.key_keyowner, names.key_public_key,
                                DataDecryptionInEffect(names), closing_line);
  }
  return requests;
}

// Which of the two arrangements a region is written under, decided by what the
// region said about its keys.
//
// A region whose data name a key the tool holds said outright what its data are
// under, so its block stays under that key and it carries no key of its own.
// Where the data name no such key, §34.5.27's arrangement is the one the region
// asked for: the tool makes a key for the region, and every key block that
// region designated a reader for carries that made key. A region that
// designated no reader the tool holds a key for is left with neither, which is
// a region there is nothing to encrypt.
// The report a region asking for a digest under an algorithm this
// implementation does not provide is owed.
//
// §34.5.22.2 has the encrypting tool generate the message digest "using the
// algorithm specified by the digest_method pragma expression", so a region
// asking for a digest under an identifier is asking for that algorithm's value
// and no other. ProtectDigestBlockDirectives
// (preprocessor/protect_digest_block.cpp) writes nothing where it cannot
// compute one, which is the right answer where it stands -- a digest is the
// value the named algorithm produces or it is nothing, and a block written
// under another algorithm would be worse -- but it holds no engine to say so.
// Saying so is what leaves an author knowing the file carries nothing to detect
// tampering with.
//
// The report says nothing about which half of Table 34-4 the identifier came
// from, where the one for §34.5.11.2's cipher does. Both halves would be the
// same answer here: §34.5.21.2 marks sha1 and md5 required, this implementation
// provides both, and ProtectDigestIsAvailable
// (preprocessor/protect_digest.cpp) answers for exactly the required
// identifiers, so an identifier it cannot compute is one the table left
// optional. Writing the other half would be writing a sentence no input can
// reach. The cipher's report keeps both because §34.5.11.2 marks des-cbc
// required and this implementation provides it under no identifier at all,
// which #3430 covers.
//
// A region asking for no digest is refused nothing, and neither is one naming
// no identifier: §34.5.21 gives the keyword a default, and the default is one
// this implementation provides.
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

// The report a region naming a cipher for its own keys that this implementation
// does not provide is owed.
//
// §34.5.24.2 has the region's keys encrypted under the algorithm the key_method
// expression names and has the identifier unchanged in the output file. This
// tool has one cipher, so the two rules pull one field two ways: writing the
// author's identifier out unchanged would state a cipher the block is not
// under, and encrypting under the identifier written is what it cannot do.
// Refusing the region settles it. Every source this tool accepts then has its
// identifier unchanged, because the only identifiers it accepts are the one it
// writes and none at all, and every envelope states the cipher its keys are
// really under. §34.5.11.2 is settled the same way for the cipher the data are
// under.
//
// A region whose keys travel in no key block is refused nothing: none of its
// keys is encrypted, so no cipher was asked for. Neither is one naming no
// identifier, §34.5.24 leaving the place empty rather than filled by the
// author.
void ReportUnprovidedKeyMethod(const RegionKeyReader& in_effect,
                               const RegionEncryption& how, DiagEngine* diag,
                               uint32_t file_id) {
  if (diag == nullptr || how.key_blocks.directives.empty()) return;
  std::string_view stated = ProtectPragmaValueBody(in_effect.key_method);
  if (stated.empty() || stated == kDataMethod) return;
  std::string message(
      "protect pragma key_method asks for an encryption algorithm this "
      "implementation does not provide: ");
  message.append(stated);
  message.append(IsRequiredProtectEncryptionAlgorithm(stated)
                     ? ", which IEEE 1800-2023 Table 34-3 requires of every "
                       "implementation"
                     : ", which IEEE 1800-2023 Table 34-3 does not require of "
                       "every implementation");
  diag->Error(LineOf(file_id, in_effect.key_method_line), message,
              Subclause("34.5.24.2"));
}

// The reports a region designating a key by a name the entity in effect beside
// it holds no key under is owed.
//
// §34.5.12.2, §34.5.18.2 and §34.5.25.2 each state the rule under ENCRYPTION
// INPUT, which is the tool being handed a text to seal, and until #3279 no
// encrypting run made any of the three: RunEnvelopeEncryption (driver/main.cpp)
// constructs no Preprocessor, so the three Preprocessor::Check*Keyname
// functions that state the rule on the reading side were never reached. What an
// author got instead was silence and a file. A region whose designations reach
// no key is returned exactly as it was written, so a mistyped name shipped the
// design in the clear and the run reported nothing.
//
// The entity each name is read against is the one in effect beside it, which is
// what ProtectKeynameReachesNoKey (preprocessor/protect_keywords.h) asks, and
// the reading side asks the same function so that one rule is enforced once.
// §34.5.16 is what fills the digest's entity where the text named none: a
// design silent about whose key its digest is under has it under the entity its
// data name.
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

// What §34.5.22 has settled about a region's digests by the time the region
// closes, apart from the key, which is not known until the region's own key is.
//
// Each part is read where the region ends rather than where the region opens,
// the scope of every one of these keywords being lexical: an expression written
// inside the region is as much in effect for it as one written ahead of it, and
// the value standing at the end is the one the region's blocks belong to.
ProtectDigestBlockPolicy DigestPolicyFor(const RegionKeyReader& in_effect) {
  ProtectDigestBlockPolicy policy;
  policy.requested = in_effect.digest_requested;
  // §34.5.22 has the digest generated under the algorithm the digest_method
  // pragma expression specifies, which is that keyword's default where the text
  // named none.
  policy.method =
      in_effect.digest_method.empty()
          ? std::string(kDefaultDigestMethod)
          : std::string(ProtectPragmaValueBody(in_effect.digest_method));
  // §34.5.21 has that identifier unchanged wherever it is written out, and the
  // key block of a signed region is one of the places it is written. It is kept
  // as the source spelled it, and left empty where the source spelled nothing:
  // the default filling the field above is this implementation's and not the
  // author's, so a block claiming the author wrote it would be claiming
  // something the text never said.
  policy.stated_method = std::string(in_effect.digest_method);
  // §34.5.22 has the digest then encrypted under the cipher digest_key_method
  // names, and §34.5.17 fills that place from the cipher the region's data are
  // under where the text named none. The envelope this tool writes states its
  // own cipher for the data, so leaving the identifier empty is what sends a
  // reader to it rather than to whichever cipher the input happened to name.
  //
  // It is the pragma_value as the source wrote it, quotes and all where it had
  // them, because §34.5.17 has the identifier unchanged wherever it is written
  // out and a value written bare that came back in quotes has been changed.
  policy.key_method = std::string(in_effect.digest_key_method);
  // §34.5.18.2 has the name of the key a region's digests are under encoded in
  // the key block of a signed region rather than written in the clear, so the
  // name travels here to be written there. It is the pragma_value as the source
  // wrote it, and empty where the source wrote none: §34.5.18 fills that place
  // from the name the region's data are under, which the envelope settles for
  // itself.
  policy.keyname = std::string(in_effect.names.digest_keyname);
  return policy;
}

RegionEncryption RegionEncryptionFor(const RegionKeyReader& in_effect,
                                     const ReadRegion& region,
                                     std::string_view exchange_key,
                                     const ProtectKeyList& keys,
                                     uint32_t closing_line) {
  RegionEncryption how;
  how.digest = DigestPolicyFor(in_effect);
  std::string_view named = RegionKey(in_effect.names, exchange_key, keys);
  if (!named.empty()) {
    how.key = named;
    // §34.5.16 has the entity a region named for its digest select the key
    // encrypting the digest block, so a region naming one whose key the tool
    // holds puts its digest under that key. Where those names reach none,
    // §34.5.20 fills the place from the key the data are under: such a region
    // carries no key block for a digest key of its own to travel in.
    std::string_view own = RegionDigestKey(in_effect.names, keys);
    how.digest.key = own.empty() ? named : own;
    return how;
  }
  ProtectKeyBlockRequests requests =
      region.written_inside.key_blocks.Empty()
          ? DesignatedKeyBlocks(in_effect.names, closing_line)
          : region.written_inside.key_blocks;
  how.key_blocks = ProtectKeyBlocksFor(
      requests, region.body, keys,
      EnvelopeBlockEncoding(region.written_inside.encoding), how.digest);
  how.key = how.key_blocks.data_key;
  // A region whose keys travel in key blocks has a key of its own for its
  // digests, made beside them and carried in the same blocks, so the digest of
  // its data block is under that key rather than under the data's.
  how.digest.key = how.key_blocks.digest_key;
  return how;
}

// The text an encryption envelope leaves behind once the directive closing it
// has been read.
//
// A region with a key to be encrypted under becomes the decryption envelope
// standing in its place. A region left without one -- the entity it names
// having supplied no key to this tool -- is not transformed at all: there is
// nothing to encrypt it under, so the directives that delimited it and the
// text between them go back exactly as the source wrote them, rather than as
// an envelope whose block stands for nothing.
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
  // §34.5.2.2 has the expression that closed the region replaced, in what the
  // encrypting tool writes out, by the one §34.5.4 defines. It is the word that
  // is replaced and not the directive carrying it, so the line goes through the
  // same transformation the opening one did and every expression written beside
  // the word is carried on to describe the envelope standing in the region's
  // place.
  std::string closing_directive =
      TransformedDelimiterLine(line, delimiter, kEndDecryptionKeyword);
  EncryptionEnvelope envelope;
  envelope.begin_directive = region.opening_directive;
  envelope.body = region.body;
  envelope.end_directive = closing_directive;
  // §34.5.5 asks for the expression present in the encryption envelope, so it
  // is taken from what the region wrote between its own delimiters rather than
  // from what merely stands in effect over it. An expression written outside
  // the region has its own treatment there: it is copied into the output stream
  // unchanged, which is what carrying the text across as its own bytes does,
  // and lifting it into the envelope as well would write it out twice.
  envelope.author = region.written_inside.author;
  // §34.5.6 asks the same of whatever further the region offered about that
  // author, and it is taken from the same place for the same reason: the
  // subclause asks for the expression present in the encryption envelope, and
  // one written outside the region already has its own treatment there -- it is
  // copied into the output stream unchanged where it stands.
  envelope.author_info = region.written_inside.author_info;
  // §34.5.30.2 asks for the comment found in the begin-end whose data block it
  // is output ahead of, so it is taken from the same place for the same reason
  // the two above are: one written outside the region is copied into the output
  // stream unchanged where it stands, and lifting it into the envelope as well
  // would write it out twice.
  envelope.comment_directives = region.written_inside.comment_directives;
  // Everything a reader needs to open this envelope's blocks is taken from what
  // stands in effect where the region closes rather than from what the region
  // wrote between its own delimiters. §34.4 makes the scope of a protect pragma
  // keyword lexical, so a value written ahead of the region is as much this
  // region's as one written inside it, and an envelope stating it is stating
  // what was in effect where it was written.
  //
  // §34.5.1.2 asks for exactly this: "protected envelopes should be completely
  // self-contained to avoid any undesired interaction when multiple encrypted
  // models exist in the decryption input stream". An envelope left to what its
  // region restated relies on text standing ahead of it, and §34.5.31 has the
  // reset every envelope ends with put the keywords back to their defaults, so
  // the second envelope of a text stating a value once would be read under
  // nothing: the value it needed was taken away by the envelope before it.
  // #3255 covers the reset, which does not yet do what §34.5.31 defines, and
  // #3275 is this.
  //
  // The three the region restates instead are the three whose subclauses ask
  // for what the encryption envelope itself held: §34.5.5's author, §34.5.6's
  // author_info and §34.5.30's comment. Each has its own treatment for a value
  // written outside the region -- it is copied into the output stream unchanged
  // where it stands -- and none of the three is anything a block is opened
  // with.
  envelope.names = in_effect.names;
  envelope.digest_method = in_effect.digest_method;
  envelope.digest_key_method = in_effect.digest_key_method;
  envelope.key_method = in_effect.key_method;
  envelope.requested_encoding = region.written_inside.encoding;
  return DecryptionEnvelopeText(envelope, how);
}

}  // namespace

std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key,
                             const ProtectKeyList& keys, DiagEngine* diag,
                             uint32_t file_id) {
  // With neither a key of one's own nor keys supplied under the names that
  // select them, there is nothing any region could be encrypted under, so the
  // text stands as it is written.
  //
  // What a caller holding an engine is still owed is the reading. §34.5.1
  // makes a region opened inside an open one an error in the text itself, and a
  // text carries that error whether or not a key was supplied to act on it, so
  // a caller that can report is told rather than handed its text back in
  // silence. Skipping the reading here would leave an author who ran this half
  // without a key unable to tell an input that was well formed from one nothing
  // looked at.
  //
  // The text is the same either way. A region reaching no key is not
  // transformed at all -- its delimiters and the lines between them go back as
  // the source wrote them -- and every line outside a region is carried across
  // as its own bytes, so reading a keyless text through returns exactly what
  // was handed in. The shortcut is kept for the caller with nowhere to report
  // to, which is the caller it saves the reading for.
  if (diag == nullptr && exchange_key.empty() && keys.Empty()) {
    return std::string(source_text);
  }
  std::string transformed;
  ReadRegion region;
  // What the text read so far has said about the key the data are under. The
  // scope of a protect pragma keyword is lexical, so a name written before a
  // region is as much in effect inside it as one written between its
  // delimiters, and it is the value standing where a region ends that selects
  // the key that region is encrypted under.
  RegionKeyReader in_effect;
  // Where the reading stands with respect to the models this text has sealed
  // inside it already. §34.5.3 has the lines of one of those read as cleartext
  // rather than as description, so this is consulted ahead of everything the
  // reading does with a line.
  PreviouslyProtectedBlock previously_protected;
  bool in_envelope = false;
  // Which line of the input the reading stands on, counted from one as the
  // reports name it. A report about a line of a source description carries the
  // position of that line, and the only thing that knows where a line stood in
  // the text is the walk that split the text into lines.
  uint32_t line_num = 0;
  for (std::string_view line : SplitLines(source_text)) {
    ++line_num;
    SourceLoc loc = LineOf(file_id, line_num);
    InputLine input = ReadInputLine(line, &previously_protected, diag, loc);
    TakeKeyNamesOutsideProtectedBlock(line, line_num,
                                      input.previously_protected, &in_effect);
    DelimiterMatch delimiter = input.delimiter;
    // §34.5.2.2 has the closing expression state, in the input cleartext, where
    // the region that is to be encrypted stops. The region therefore ends at
    // the line the word is written on rather than at the end of the text or at
    // some later delimiter, so this is where the lines gathered so far become a
    // block and the lines after it go back to being carried across.
    if (in_envelope && delimiter.kind == EnvelopeDelimiter::kEnd) {
      RegionEncryption how =
          RegionEncryptionFor(in_effect, region, exchange_key, keys, line_num);
      // §34.5.27 has every key block of one envelope encode the same data
      // decryption key data, so a region whose data decryption pragma
      // expressions changed value between two of them is reported rather than
      // left carrying blocks that open onto different accounts of one key. The
      // report stands at the block that stopped agreeing rather than here,
      // where the region merely closed.
      if (diag != nullptr && how.key_blocks.data_changed_line != 0) {
        diag->Error(
            LineOf(file_id, how.key_blocks.data_changed_line),
            "protect pragma data decryption expressions change value between "
            "the key_block pragma expressions of one encryption envelope",
            Subclause("34.5.27"));
      }
      ReportUnprovidedDataMethod(in_effect, diag, file_id);
      ReportUnavailableDigestMethod(in_effect, diag, file_id);
      ReportUnprovidedKeyMethod(in_effect, how, diag, file_id);
      ReportKeynamesReachingNoKey(in_effect, keys, diag, file_id);
      transformed.append(
          ClosedRegionText(region, in_effect, line, delimiter, how));
      in_envelope = false;
    } else if (in_envelope) {
      // §34.5.1 rules out a second opening expression here, this region not
      // having been closed yet, so a line carrying one is reported before it is
      // taken as text of the region.
      ReportNestedRegion(delimiter, diag, loc);
      // §34.5.3 and §34.5.4 have the two expressions delimiting a previously
      // generated block, and everything between them, encrypted into the block
      // of the envelope enclosing them. Adding the line unread is what does
      // that: an already-protected model travels into the larger one as the
      // bytes it is written with.
      AppendEnvelopeLine(line, line_num, input.previously_protected, &region);
    } else if (delimiter.kind == EnvelopeDelimiter::kBegin) {
      in_envelope = true;
      region.opening_line = line;
      region.opening_directive =
          TransformedDelimiterLine(line, delimiter, kBeginDecryptionKeyword);
      region.source_body.clear();
      region.body.clear();
      region.written_inside = {};
      // What the region wrote for itself is collected apart from what stands
      // over it, but the coding scheme is not one of the things collected: it
      // decides how the region's own lines are read, and the scheme in effect
      // where the region opens is in effect inside it until the region says
      // otherwise.
      region.written_inside.encoding = in_effect.encoding;
    } else {
      // Text no encryption envelope contains is carried across as the bytes it
      // was written with, whatever it says.
      transformed.append(line);
    }
  }
  // A region whose closing expression was never written closes no envelope, so
  // nothing was replaced: the opening directive and the lines after it are
  // text of the source like any other, and go back as they stand.
  if (in_envelope) {
    transformed.append(region.opening_line);
    transformed.append(region.source_body);
  }
  return transformed;
}

}  // namespace delta
