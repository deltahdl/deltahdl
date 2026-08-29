// The reading that takes the line an announcing protect pragma keyword speaks
// for.
//
// §34.5.13, §34.5.14, §34.5.15, §34.5.19, §34.5.20, §34.5.22, §34.5.26 and
// §34.5.27 each define their keyword as the pragma_keyword standing alone and
// put the value it announces on the line beneath it. None of those values is
// written where the expression carrying the keyword is read, so all eight are
// read here instead, when the line the keyword spoke for arrives.
//
// Each of those lines carries an encoded value rather than the bytes
// themselves, so all eight reach §34.5.9's reading through one call:
// Preprocessor::ReadEncodedProtectValue turns the characters into bytes under
// the coding scheme in effect and spends the byte count that scheme stated.

#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {

// §34.5.27: the block a key_block expression announces is first read in the
// encoded form, the encoding is reversed, and then the block is internally
// decrypted. The resulting text is then parsed to determine the keys required
// to decrypt the data block.
//
// What a key block recovers to is protect pragma directives, so parsing it is
// running it through the same reading every directive of the source goes
// through: what those directives put in effect is what the region's data block
// is then opened with, and no second grammar has to exist for the inside of a
// block. It contributes no text of its own -- a key block holds keys rather
// than design -- so what that reading produces is dropped.
//
// The key the block itself is opened with is the one §34.5.25 and §34.5.26
// reach: the entity named for the region's own keys, combined with whichever
// designation of one of that entity's keys stands before the block. Those are
// restated ahead of each block, their scope being lexical, so an envelope
// carrying several reaches a different key for each.
//
// A block that does not open is passed over in silence. §34.5.27 has several
// key blocks stand for alternative decryption keys to one envelope, so a reader
// holding one entity's key is expected to be unable to open the blocks written
// for the others, and reporting each of those would make the ordinary case
// noisy. What no key at all costs is the data block, which says so where it is
// reached.
//
// The recovered text is read one step deeper than the text carrying it. Reading
// it is reading a source text found inside another, and bounding that the way
// an inclusion is bounded is what keeps a block whose content names a further
// block from being followed without end.
bool Preprocessor::TakeKeyBlockValue(std::string_view line, SourceLoc loc,
                                     int depth) {
  if (!key_block_value_next_) return false;
  key_block_value_next_ = false;
  std::string block;
  // A line that cannot be read out of the scheme in effect carries no block,
  // and the line is consumed either way: the keyword above it said the line is
  // key material, so it is not text of the design whether or not a block came
  // out of it.
  if (!ReadEncodedProtectValue(Trim(line), loc, &block)) return true;
  std::string content;
  if (!DecryptProtectedBlock(
          block, ProtectKeyBlockKey(protect_keywords_, config_.protect_keys),
          &content)) {
    return true;
  }
  // The block is run for what it defines and its text is appended nowhere, so
  // its lines are not lines of the output and must not be recorded as such.
  // Recording them would name lines the output does not have and would displace
  // every line written after this one.
  bool was_recording = recording_origins_;
  recording_origins_ = false;
  ProcessSource(content, loc.file_id, depth + 1);
  recording_origins_ = was_recording;
  // §34.5.22 owes this block a digest of its own, written immediately after it,
  // so what the block recovered to is held for the digest that follows. The key
  // that digest is under is read only now, because the block just read is what
  // carried it: §34.5.20 puts the digest's key inside the very block whose
  // digest is checked with it, so a reader learns the key by opening the block
  // and then checks that the block it opened is the one that was sealed.
  digest_target_ = {content, std::string(DigestBlockKeyInEffect())};
  return true;
}

// §34.5.20: a line a digest_decrypt_key expression announces holds the encoded
// value of the key that will decrypt the region's digest block, so the line is
// that key rather than a line of the design, and it is read as the value the
// keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.20 has that value encoded as the encoding pragma expression specifies,
// so reading it back out of the scheme in effect is what leaves the key itself
// in hand. A key travels the same whichever scheme the envelope chose to spell
// it with.
//
// A line that is not something the scheme in effect writes carries no key, and
// the region's digests are left under the key its data are under -- the default
// this subclause settles for a text that specified none. Saying so is what
// keeps a digest from being reported as one the block disagrees with when what
// really happened is that no key was recovered to check it with.
bool Preprocessor::TakeDigestDecryptKeyValue(std::string_view line,
                                             SourceLoc loc) {
  if (!digest_decrypt_key_value_next_) return false;
  digest_decrypt_key_value_next_ = false;
  std::string key;
  if (!ReadEncodedProtectValue(Trim(line), loc, &key)) return true;
  // §34.5.16.2: a decryption key recovered here is one of the three
  // designations the values of which are unique for the digest_keyowner in
  // effect, so it is held to that whether it was written against the keyword
  // or, as §34.5.20.1 writes it, on the line beneath the keyword.
  CheckDigestDesignationValue(kDigestDecryptKeyKeyword, key, loc);
  digest_decrypt_key_ = std::move(key);
  return true;
}

// §34.5.22: a line a digest_block expression announces holds the encoded value
// of the message digest of the block this one immediately follows, so the line
// is that digest rather than a line of the design, and it is read as the value
// the keyword was left waiting for.
//
// What the digest is for is authenticating the block above it: the digest the
// block carries is decrypted with the key the region named for it, a digest is
// generated from the data the reading recovered, and the two are compared. Two
// that disagree say the digest or the encrypted data was altered after the
// input data was encrypted, and which of the two it was is not something the
// comparison can tell.
//
// A digest this reader cannot open is passed over in silence. §34.5.27 has the
// key blocks of one envelope stand for alternative ways in, so a reader holding
// one entity's key is expected to be unable to open the blocks written for the
// others, and each of those is owed a digest a reader of another block has no
// business checking. Only two digests that were both reached and disagree say
// anything happened to the data.
//
// The block being checked is spent by the check, so a second digest written
// after it finds nothing to announce it rather than checking the same block
// twice.
bool Preprocessor::TakeDigestBlockValue(std::string_view line, SourceLoc loc) {
  if (!digest_block_value_next_) return false;
  digest_block_value_next_ = false;
  ProtectDigestTarget target = std::move(digest_target_);
  digest_target_ = ProtectDigestTarget();
  std::string block;
  if (!ReadEncodedProtectValue(Trim(line), loc, &block)) return true;
  last_digest_block_check_ =
      CheckProtectDigestBlock(block, target, DigestMethodInEffect());
  if (last_digest_block_check_ == ProtectDigestCheck::kAltered) {
    diag_.Error(loc,
                "protect pragma digest block disagrees with the block it "
                "follows, so one of the two was altered after encryption",
                Subclause("34.5.22"));
  }
  return true;
}

// §34.5.14: the line a data_decrypt_key expression announces holds the encoded
// value of the key that will decrypt the region's data block, so the line is
// that key rather than a line of the design, and it is read as the value the
// keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.9 has every encoded value of an envelope written under the coding
// scheme that envelope declares, so reading it back out of that scheme is what
// leaves the key itself in hand. A key travels the same whichever scheme the
// envelope chose to spell it with.
//
// A line that is not something the scheme in effect writes carries no key, and
// the region is left with none. Saying so is what keeps a block from being
// reported as one the supplied key does not fit when what really happened is
// that no key was recovered to try.
bool Preprocessor::TakeDataDecryptKeyValue(std::string_view line,
                                           SourceLoc loc) {
  if (!data_decrypt_key_value_next_) return false;
  data_decrypt_key_value_next_ = false;
  std::string key;
  if (!ReadEncodedProtectValue(Trim(line), loc, &key)) return true;
  // §34.5.10.2: a decryption key recovered here is one of the three
  // designations the values of which are unique for the data_keyowner in
  // effect, so it is held to that whether it was written against the keyword
  // or, as §34.5.14.1 writes it, on the line beneath the keyword.
  CheckDataKeyDesignationValue(kDataDecryptKeyKeyword, key, loc);
  data_decrypt_key_ = std::move(key);
  return true;
}

// §34.5.26: the keyword announcing a public key says that the next line of the
// file holds that key's encoded value, so the line is the designation of a key
// rather than a line of the design, and it is read as the value the keyword
// was left waiting for. Being a designation, it is held to what §34.5.23 and
// §34.5.26 require of one, exactly as a designation written against a keyword
// is.
//
// The whole of the line is the value, taken without the whitespace that
// positioned it. What the line carries is the key's encoded value rather than
// the key, and §34.5.26 sends the reading to the encoding pragma expression in
// effect for the coding scheme it was encoded under, so reading it back out of
// that scheme is what leaves the designation itself in hand. A key designated
// this way therefore reaches the same key of the same entity whichever scheme
// the text chose to spell it with.
//
// A line that is not something the scheme in effect writes designates no key
// at all, and saying so is what keeps a text from being read under a scheme it
// was not written under without anything remarking on it.
//
// Only a line inside a decryption envelope is read this way. An announcement
// there is one an encrypting tool wrote into a protected block along with the
// value beneath it, which is the arrangement §34.5.26 has that tool produce.
// Outside every envelope there is no protected block for a public key to have
// been used for, so the text beneath the announcement is text of the source
// like any other and is left to whatever reads it.
bool Preprocessor::TakeKeyPublicKeyValue(std::string_view line, SourceLoc loc) {
  if (!key_public_key_value_next_) return false;
  key_public_key_value_next_ = false;
  std::string value;
  // A line that cannot be read out of the scheme in effect designates no key,
  // and the line is consumed either way: the keyword above it said the line is
  // key material, so it is not text of the design whether or not the key came
  // out of it.
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kKeyPublicKeyKeyword, value);
  CheckKeyBlockDesignation(kKeyPublicKeyKeyword, value, loc);
  return true;
}

// §34.5.13: the keyword announcing the public key a region's data are under
// says that the next line of the file holds that key's encoded value, so the
// line is the designation of a key rather than a line of the design, and it is
// read as the value the keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.13 sends the reading to the encoding pragma expression currently in
// effect for the coding scheme it was encoded under, so reading it back out of
// that scheme is what leaves the designation itself in hand. A key designated
// this way therefore reaches the same key of the same entity whichever scheme
// the text chose to spell it with.
//
// Being a designation, it is held to what §34.5.13 requires of one alongside
// the name the region gave its key, exactly as a designation written against a
// keyword is.
//
// A line that is not something the scheme in effect writes designates no key at
// all, and saying so is what keeps a text from being read under a scheme it was
// not written under without anything remarking on it. The line is consumed
// either way: the keyword above it said the line is key material, so it is not
// text of the design whether or not a key came out of it.
//
// Only a line inside a decryption envelope is read this way. §34.5.13 has an
// encrypting tool write this keyword into each protected block the designation
// was used for, with the value beneath it, so an announcement there is one that
// tool produced. Outside every envelope there is no protected block for a
// public key to have been used for, so the text beneath the announcement is
// text of the source like any other and is left to whatever reads it.
bool Preprocessor::TakeDataPublicKeyValue(std::string_view line,
                                          SourceLoc loc) {
  if (!data_public_key_value_next_) return false;
  data_public_key_value_next_ = false;
  std::string value;
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kDataPublicKeyKeyword, value);
  // §34.5.10.2: the public key just read designates a key of the data_keyowner
  // in effect, so it is held to being unique for that entity like the name
  // beside it. §34.5.13.1 writes it on the line beneath its keyword, which is
  // why the expression-shaped check does not see it.
  CheckDataKeyDesignationValue(kDataPublicKeyKeyword, value, loc);
  CheckDataDesignationAgreement(loc);
  return true;
}

// §34.5.19: the keyword announcing the public key a region's digest is under
// says that the next line of the file holds that key's encoded value, so the
// line is the designation of a key rather than a line of the design, and it is
// read as the value the keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.19 sends the reading to the encoding pragma expression currently in
// effect for the coding scheme it was encoded under, so reading it back out of
// that scheme is what leaves the designation itself in hand. A key designated
// this way therefore reaches the same key of the same entity whichever scheme
// the text chose to spell it with.
//
// Being a designation, it is held to what §34.5.19 requires of one alongside
// the name the region gave its digest's key, exactly as a designation written
// against a keyword is.
//
// A line that is not something the scheme in effect writes designates no key at
// all, and saying so is what keeps a text from being read under a scheme it was
// not written under without anything remarking on it. The line is consumed
// either way: the keyword above it said the line is key material, so it is not
// text of the design whether or not a key came out of it.
//
// Only a line inside a decryption envelope is read this way. §34.5.19 has an
// encrypting tool write this keyword into each protected block the designation
// was used for, with the value beneath it, so an announcement there is one
// that tool produced. Outside every envelope there is no protected block for a
// public key to have been used for, so the text beneath the announcement is
// text of the source like any other and is left to whatever reads it.
bool Preprocessor::TakeDigestPublicKeyValue(std::string_view line,
                                            SourceLoc loc) {
  if (!digest_public_key_value_next_) return false;
  digest_public_key_value_next_ = false;
  std::string value;
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kDigestPublicKeyKeyword, value);
  // §34.5.16.2: the public key just read designates a key of the
  // digest_keyowner in effect, so it is held to being unique for that entity
  // like the name beside it. §34.5.19.1 writes it on the line beneath its
  // keyword, which is why the expression-shaped check does not see it.
  CheckDigestDesignationValue(kDigestPublicKeyKeyword, value, loc);
  CheckDigestDesignationAgreement(loc);
  return true;
}

// §34.5.9 gives a reading of an encoded value three ways to fail, and they are
// different things to be told.
//
// The scheme may be one nothing here provides. Table 34-2 names four
// identifiers and leaves further ones to the implementation, so one outside
// both sets stands for no writing at all: there is nothing to measure the
// characters against, however well formed they are.
//
// Or the scheme may be one this tool has and the value may not be something
// that scheme writes, which says it was written under a different scheme from
// the one standing where it was written. Reporting the two alike would leave an
// author unable to tell an envelope this tool cannot open from one whose
// description of itself does not match what it carries.
//
// Or the characters may be that scheme's writing and stand for a quantity the
// same expression contradicts. Measuring before the value is handed on keeps a
// value of the wrong size from being reported as a key that does not fit.
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

// §34.5.9.2 defines the count as the number of bytes in *the* original block of
// data, so it describes the one value written under it rather than the scheme
// the envelope is in. The scheme outlives the value and the count does not:
// left standing, the count an envelope stated for one block would be measured
// against the next value read, and against every value the text recovered out
// of that block goes on to carry -- a designation of a key that a whole block's
// length would never match.
//
// The scheme itself is left exactly as it was written. A text that stated a
// coding scheme once and wrote several values under it stated it for all of
// them, which is why only the count is taken away.
void Preprocessor::SpendEncodedValueSize() {
  ProtectKeywordValue held = protect_keywords_.ValueOf(kEncodingKeyword);
  if (held.defaulted) return;
  ProtectEncoding encoding = ParseProtectEncoding(held.value);
  if (!encoding.has_bytes) return;
  encoding.has_bytes = false;
  protect_keywords_.Apply(kEncodingKeyword, ProtectEncodingValue(encoding));
}

// §34.3: envelope decryption recognizes a decryption envelope and puts the
// cleartext of the region it stands for back in its place, for the compilation
// step that follows. §34.5.15.2 has the data_block expression indicate "that a
// data block begins on the next line in the file", so the line carrying that
// region is the one acted on here, and the cleartext is emitted where the
// envelope was written: the text that leaves the preprocessor is the design.
//
// The line is reached the way §34.5.27's key block and §34.5.22's digest block
// are reached, all three keywords being spelled standing alone by their own
// subclauses: ApplyAnnouncedBlockKeywords records that the keyword was written,
// and Preprocessor::TookAnnouncedValue (preprocessor/preprocessor.cpp) offers
// it the line beneath. Only an announcement made inside a decryption envelope
// is recorded, so a data_block expression written anywhere else describes
// something other than a protected region and the line beneath it is left to
// whatever reads it.
//
// Where the user's key is not the one the region was encrypted under, no
// cleartext can be put back, and saying so is the only way the missing design
// does not read as an empty one.
//
// What the recovered text is then put through is what §34.3.2 settles. The
// text a region records is source text like any other, so it may hold macro
// usages and it may hold further decryption envelopes -- and each of those is
// read only once the envelope that sealed it has been replaced, because until
// then it is inside a block rather than inside the source. Handing the
// cleartext back to the source loop is what puts it in that order: it is
// substituted for the envelope first, and the loop then reaches its macros and
// its envelopes the same way it reaches those of a file, one step behind the
// replacement that produced them.
//
// §34.5.9 settles the other half of reading such a block: the block is
// characters and what it records is bytes, so the scheme in effect turns the
// one into the other, and the count stated ahead of the block says how many
// bytes should come out. Both are spent where every encoded value of an
// envelope is read, so a block of the wrong size is turned away there -- before
// any key is offered to it, and so never reported as a key that does not fit.
bool Preprocessor::TakeDataBlockValue(std::string_view line, SourceLoc loc,
                                      int depth, std::string& output) {
  if (!data_block_value_next_) return false;
  data_block_value_next_ = false;
  std::string block;
  // A line that cannot be read out of the scheme in effect carries no block,
  // and the line is consumed either way: the keyword above it said the line is
  // where the block begins, so it is not text of the design whether or not a
  // block came out of it.
  if (!ReadEncodedProtectValue(Trim(line), loc, &block)) return true;
  // §34.5.14 has the key a key block carried open the data block that block was
  // written beside, so it is spent here rather than left standing over whatever
  // the text goes on to hold. A key made for one region says nothing about the
  // next, and an envelope that carried none of its own is read under the names
  // it did write rather than under a key some earlier envelope made for itself.
  // Taking a copy is what lets the key be put away before it is used.
  std::string region_key(ProtectKeyInEffect());
  data_decrypt_key_.clear();
  // §34.5.11.2: the data_method states the algorithm the data block is to be
  // decrypted with. This implementation provides one cipher and states its own
  // identifier for it, so a block naming any other algorithm is a block it
  // cannot read -- and reading it under the cipher it does provide would hand
  // back whatever those bytes happen to become rather than the design.
  //
  // A block naming no algorithm is left alone: the keyword has a default and an
  // envelope this tool produced always names its own, so the ones that arrive
  // without a name came from somewhere that took the default with them.
  ProtectKeywordValue method = protect_keywords_.ValueOf(kDataMethodKeyword);
  if (!method.defaulted && !method.value.empty() &&
      method.value != kDataMethod) {
    diag_.Error(loc,
                "protect pragma data block states an encryption algorithm this "
                "implementation does not provide: " +
                    method.value,
                Subclause("34.5.11.2"));
    return true;
  }
  std::string cleartext;
  if (!DecryptProtectedBlock(block, region_key, &cleartext)) {
    diag_.Error(loc,
                "protect pragma data block cannot be decrypted with the key "
                "supplied",
                Subclause("34.3.2"));
    return true;
  }
  // §34.5.22 owes this block a digest of its own, written immediately after it,
  // so what the block recovered to is held for the digest that follows,
  // together with the key that digest is under. Both are taken before the
  // recovered text is read through, because that text may carry envelopes of
  // its own and each of those spends its keys and checks its digests as it
  // goes; installing this one afterwards is what leaves the outer block's
  // digest checked against the outer block.
  ProtectDigestTarget target{cleartext, std::string(DigestBlockKeyInEffect())};
  // Nothing of the envelope's own is left standing over the recovered text
  // while it is read: a key block of this envelope was the last thing
  // recovered, and a digest_block expression the design itself carries follows
  // no block of the design.
  digest_target_ = ProtectDigestTarget();
  // §34.5.20 has a key a key block carried open the digests of the region that
  // block belongs to, so it is spent here alongside the key that opened the
  // data rather than left standing over whatever the text goes on to hold. The
  // digest still to be checked holds the key it needs already.
  digest_decrypt_key_.clear();
  output.append(ProcessSource(cleartext, loc.file_id, depth));
  digest_target_ = std::move(target);
  return true;
}

}  // namespace delta
