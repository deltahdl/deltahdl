// §34.5.27, for the protect pragma keyword that carries the keys of an
// encrypted region, read on the side that produces one.
//
// §34.5.27.2 states two conditions on an encrypting tool's input, and they are
// the whole of what this file covers. The first:
//
//   It shall be an error if a key_block is found in an input file unless it is
//   contained within a previously generated begin_protected-end_protected
//   block, in which case it is ignored.
//
// and the second:
//
//   It shall be an error if the data decryption pragma expressions change
//   value between key_block pragma expressions of a single encryption
//   envelope.
//
// What the first costs an author is a block that opens onto nothing. A key
// block written where no previously generated block encloses it carries the
// keys of no envelope -- there is nothing it could have come out of, and no key
// it could have been encrypted under -- so a tool that passed over it would
// copy those characters into its output as ordinary source text.
//
// What the second costs is worse, because the blocks it produces look right.
// §34.5.27 makes several key blocks alternative ways into a single decryption
// envelope rather than ways into several, so they all encode the same data
// decryption key data. A region that changed one of those expressions between
// two of its designations has asked for blocks that cannot all be the keys of
// the same data, and a reader holding the second entity's key would open a
// block describing data the envelope does not carry.
//
// Both cost the report rather than the transformation. §34.5.27 says nothing
// about stopping, so the reading runs to the end of the input and the blocks
// the region asked for are still written. Each case below therefore names the
// report rather than asking whether the text came back.
//
// §34.5.27.1's syntax -- the keyword written as the bare word, with the block
// on the line beneath it -- is covered in
// test_preprocessor_subclause_34_05_27_01.cpp. This file is about where a block
// may stand and what several of them have to agree on, so it is the encrypting
// half of §34.3 that is driven here: src/preprocessor/protect_input_line.cpp
// decides whether a previously generated block contains a line, and
// src/preprocessor/protect_key_block.cpp measures each block a region asked for
// against the first.
//
// §34.5.23's entity and §34.5.25's key name are what designate the key a block
// is encrypted under, and a region reaches the arrangement that writes blocks
// at all by naming no key for its own data, so §34.5.12's key name is the
// expression the disagreeing regions below change. §34.5.3.1's and §34.5.4.1's
// words delimit a previously generated block, and §34.5.1.1's and §34.5.2.1's
// pair delimits a region to be encrypted.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// A key block written in the clear, as a tool reading a text would meet one.
// What it says is deliberately not a value any coding scheme writes, so nothing
// here turns on the characters being readable as a block: the rule is about
// where the expression stands.
constexpr std::string_view kKeyBlockDirective =
    "`pragma protect key_block=\"NOTAKEYBLOCKOFANYENVELOPE\"\n";

// The design the regions below enclose.
constexpr std::string_view kSealedDesign = "  initial result = 42;\n";

// The entities that provided the keys the regions' own keys travel under, and
// one key of each. §34.5.27 owes a block to each designation a region writes,
// so a region naming two of these has asked for two ways into its one envelope.
constexpr std::string_view kFirstProvider = "aegis-custody";
constexpr std::string_view kFirstProviderKeyName = "wrapping-2026";
constexpr std::string_view kFirstProviderKey = "aegis-custody-wrapping-key";
constexpr std::string_view kSecondProvider = "borealis-trust";
constexpr std::string_view kSecondProviderKeyName = "wrapping-2027";
constexpr std::string_view kSecondProviderKey = "borealis-trust-wrapping-key";
constexpr std::string_view kThirdProvider = "cerulean-vault";
constexpr std::string_view kThirdProviderKeyName = "wrapping-2028";
constexpr std::string_view kThirdProviderKey = "cerulean-vault-wrapping-key";

// The keys those three entities supplied, held under the names that select
// them. A designation reaching none of them asks for no block at all, so a
// region whose blocks are to be compared has to have every one of its
// designations reach a key.
ProtectKeyList KeysOfEveryProvider() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstProvider, kFirstProviderKeyName, kFirstProviderKey));
  keys.Add(KeyOf(kSecondProvider, kSecondProviderKeyName, kSecondProviderKey));
  keys.Add(KeyOf(kThirdProvider, kThirdProviderKeyName, kThirdProviderKey));
  return keys;
}

// One protect pragma expression with a value written against it, as a directive
// of its own.
std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// One designation of a key block's key: the entity that provided it, the name
// §34.5.12 gives the key the region's data are under standing in effect where
// the designation is made, and the name that picks the block's own key out of
// that entity's list.
//
// The data key name is written ahead of each designation rather than once for
// the region, because it is one of the data decryption pragma expressions the
// blocks are held to agreeing on: a region that writes a different one here has
// asked for its second block under an account of the data its first does not
// share.
std::string Designation(std::string_view provider, std::string_view key_name,
                        std::string_view data_key_name) {
  std::string text = Writes("key_keyowner", provider);
  text.append(Writes("data_keyname", data_key_name));
  text.append(Writes("key_keyname", key_name));
  return text;
}

// An encryption region holding `described` and then the design. The region
// names no key for its data, which is what sends it to the arrangement
// §34.5.27 writes key blocks for.
std::string Region(std::string_view described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// Envelope encryption over a source text under keys supplied by name, with the
// reports kept beside the text it produced.
//
// No exchange key is supplied at all. One would encrypt every region whatever
// it designated, and a region encrypted under it carries no key block for a
// second block to disagree with.
struct KeyedEncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit KeyedEncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, KeysOfEveryProvider(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: a block no previously generated block contains.
// ---------------------------------------------------------------------------

// The first condition at its plainest: the expression standing in an input file
// with no previously generated block anywhere in the text. There is no envelope
// whose keys it could be carrying, so it is reported, on the line the author
// wrote it on.
TEST(ProtectKeyBlockEncryptionInput, ABlockContainedByNothingIsReported) {
  std::string src = "module m;\n";
  src.append(kKeyBlockDirective);
  src.append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "key_block is written where no previously", 2,
                            "34.5.27"));
}

// The other half of the same sentence, and the input the case above is read
// against: the same expression written inside the pair of words a previously
// generated block is delimited by. It belongs to the envelope that block is, so
// §34.5.27 has it ignored rather than objected to.
TEST(ProtectKeyBlockEncryptionInput, ABlockASealedModelContainsIsIgnored) {
  std::string src = "`pragma protect begin_protected\n";
  src.append(kKeyBlockDirective);
  src.append("`pragma protect end_protected\n");
  EncryptionRun run(src);
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The region an author is about to seal is not what contains a block for the
// purpose of this rule. §34.5.27 names the previously generated
// begin_protected-end_protected block and nothing else, so a block written
// between the words that delimit a region to encrypt has still come out of no
// envelope.
TEST(ProtectKeyBlockEncryptionInput, ABlockInsideARegionToSealIsReported) {
  std::string src = Region(kKeyBlockDirective);
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "key_block is written where no previously", 2,
                            "34.5.27"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the blocks of one envelope encode one key's data.
// ---------------------------------------------------------------------------

// The accepting input the condition is read against, and the arrangement
// §34.5.27 describes: two entities designated inside one region, with the data
// decryption pragma expressions saying the same thing at both designations.
// The blocks are two ways into one envelope, so nothing is reported -- and both
// blocks really are written, which is what keeps the silence from being the
// silence of a region that asked for nothing.
TEST(ProtectKeyBlockEncryptionInput, TwoBlocksAgreeingAboutTheDataAreAccepted) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2026"));
  KeyedEncryptionRun run(Region(described));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect key_block"), 2U);
}

// The condition itself: the same two designations with §34.5.12's key name
// changed between them. The two blocks then stand for two accounts of the one
// envelope's data, which is what §34.5.27 rules out, and the report stands at
// the designation that stopped agreeing rather than where the region closed.
TEST(ProtectKeyBlockEncryptionInput,
     ADataExpressionChangedBetweenTwoBlocksIsReported) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2027"));
  std::string src = Region(described);
  KeyedEncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data decryption expressions change value",
      LineHolding(src, kSecondProviderKeyName), "34.5.27"));
}

// The blocks are still written. What the condition costs is the report, so a
// region that asked for two ways into its envelope gets two, and the design it
// enclosed is sealed rather than handed back readable.
TEST(ProtectKeyBlockEncryptionInput, TheReportedRegionIsStillGivenItsBlocks) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2027"));
  KeyedEncryptionRun run(Region(described));
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect key_block"), 2U);
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
}

// A region designating three entities, with the last two disagreeing with the
// first. It is one region that broke the rule once, so it draws one report, and
// the report names the designation that first stopped agreeing: an author shown
// the last of them would go looking for the change at a designation that says
// exactly what the one above it says.
TEST(ProtectKeyBlockEncryptionInput,
     AThirdDisagreeingBlockDrawsNoSecondReport) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2027"));
  described.append(
      Designation(kThirdProvider, kThirdProviderKeyName, "design-2028"));
  std::string src = Region(described);
  KeyedEncryptionRun run(src);
  EXPECT_EQ(run.diag.ErrorCount(), 1U);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data decryption expressions change value",
      LineHolding(src, kSecondProviderKeyName), "34.5.27"));
}

}  // namespace
