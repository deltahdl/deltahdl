// §34.5.10.1 Syntax, for the protect pragma keyword that names the entity
// whose keys a protected region's data are under.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression:
//
//   The keyword is written with an '=' and a value against it, and that value
//   is a string. A string is one written thing, so the parenthesized spelling
//   §22.5.1 also gives a pragma_value -- a list of further expressions -- is
//   not the value this keyword is defined with, its elements naming parts of
//   something rather than being the thing.
//
// That is the whole difference between this line and §34.5.9.1's, which is the
// one keyword of §34.4's table defined with a list: a list against this keyword
// would be somebody's invention, while a single written thing against that one
// invents something.
//
// What a reading draws from the expression is real, which is what separates the
// observations below from the ones a keyword nothing is taken from admits. A
// key name is a member of one entity's list of keys and names nothing outside
// it, so the value written here is half of what selects the key a region's
// block is written under and opened with. It is therefore visible in whether a
// block opens at all -- and, the entity being one of the two names §34.5.10 has
// an encrypting tool state in the clear, in the text of the envelope a region
// is turned into.
//
// All of it is preprocessor-stage. The reading of the spelling as tokens is the
// pragma grammar in src/preprocessor/preprocessor_lines.cpp, which is where the
// '=' and the value after it are recognized; src/preprocessor/protect_keywords.
// cpp tabulates the name, holds the value a directive wrote in effect from
// there on, and writes the keyword back out as a directive of an envelope;
// src/preprocessor/protect_pragma_line.cpp is where a value's spelling is told
// from a list of further expressions; src/preprocessor/protect_processing.cpp
// is the encrypting half, which takes the name off a region's own lines and
// carries it onto the envelope; and src/preprocessor/preprocessor_protect_keys.
// cpp is the reading half, where the name in effect selects the key a block is
// opened with.
//
// Every input below is written as the real `pragma directive syntax of §22.11.
// §34.5.1.1's and §34.5.2.1's words delimit the region the encrypting half is
// handed, §34.5.3.1's and §34.5.4.1's delimit the envelope that half produces,
// §34.5.12.1's key name is the designation this entity is combined with to
// reach a single key, and §34.5.15's block is what that key opens.

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity a text names as having provided the key its data are under.
constexpr std::string_view kOwner = "acme-semiconductor";

// A second entity, holding a key of its own under the very name the first one
// holds a key under. Two parties rather than one is what makes the name written
// for the entity decide anything: with a single party in the tool's hands, a
// reading that never looked at this name would reach the same key as one that
// did, and every observation below would pass either way.
constexpr std::string_view kOtherOwner = "globex-ip";

// The name given to one key of each of them, which is the designation
// §34.5.12.1 writes and the half the entity is combined with.
constexpr std::string_view kKeyName = "data-2026";

// The two keys those pairs reach. A block sealed under one of them does not
// open under the other.
constexpr std::string_view kOwnerKey = "acme-region-exchange-key";
constexpr std::string_view kOtherOwnerKey = "globex-region-exchange-key";

// The key an author holding a single key hands the encrypting half, and hands
// back to a tool reading what that half produced. It is supplied under no name
// at all, so a region carrying one is encrypted whatever its lines name.
constexpr std::string_view kExchangeKey = "one-key-of-the-authors-own";

// The design a region seals. Nothing of it survives the alphabet an encrypted
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The directive announcing the block an envelope carries, which §34.5.15.1
// spells as the keyword standing alone. Everything a block is opened under has
// to stand ahead of this, so a directive written here is the last word on the
// entity in effect where the block is read.
constexpr std::string_view kBlockDirective = "`pragma protect data_block\n";

// Whether `text` writes `written` anywhere in it.
bool Carries(std::string_view text, std::string_view written) {
  return text.find(written) != std::string_view::npos;
}

// One protect pragma directive writing `value` against `keyword` as a string,
// which is the spelling §34.5.10.1 defines its own keyword in.
//
// It serves both sides. A source text names an entity with these characters,
// and §34.5.10 has an encrypting tool state the name in the clear, so what a
// tool produced is compared against the spelling the input was built from
// rather than against a second spelling of it.
std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The directive this subclause defines, carrying `value` exactly as written
// rather than as a string. The inputs that ask what a spelling settles are
// built with this, which characters stand against the keyword being the thing
// being observed.
std::string NamesOwner(std::string_view value) {
  std::string directive = "`pragma protect data_keyowner=";
  directive.append(value).append("\n");
  return directive;
}

// The parenthesized spelling §22.5.1 gives a pragma_value, written against this
// keyword: a list of subkeyword expressions, one of them carrying the entity's
// name as a properly quoted string.
//
// It is the sharpest near miss there is to the defined value. Every character
// the syntax line calls for is on the line and in its order, and what stands
// around them is one pair of parentheses and a subkeyword nobody defined.
std::string NamesOwnerInAList(std::string_view owner) {
  std::string list = "(company=\"";
  list.append(owner).append("\")");
  return NamesOwner(list);
}

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with `described`
// and then the design between them. The design comes last so that a line the
// encryption passed over is a line that went into the block ahead of it.
std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// A user holding one key of each party, both under one key name. Which key a
// region is sealed under and opened with is then decided by the entity beside
// that name and by nothing else in the text.
ProtectKeyList KeysOfBothParties() {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kOwner), std::string(kKeyName), std::string(kOwnerKey)});
  keys.Add({std::string(kOtherOwner), std::string(kKeyName),
            std::string(kOtherOwnerKey)});
  return keys;
}

// What a user who supplied keys under the names that select them gives the
// tool.
PreprocConfig KeysConfig() {
  PreprocConfig config;
  config.protect_keys = KeysOfBothParties();
  return config;
}

// What a user holding a single key of their own gives the tool instead.
PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  return config;
}

// A reading of `src` by a tool holding a key of each party, with the
// preprocessor kept alive afterwards.
//
// What the expression leaves behind is a value in effect rather than output
// text: it belongs to the point the reading has reached rather than to any one
// directive, so it is read off the preprocessor once the whole text has passed
// through, and the diagnostics that reading raised are read beside it.
struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  explicit ReadUnderKeys(const std::string& src) : pp(mgr, diag, KeysConfig()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }
};

// The envelope the encrypting half leaves where a region holding `described`
// was written, for an author who supplied a key of each party, checked on the
// way out to be an envelope: the design it was formed from is gone from the
// text.
//
// A round trip that looked only at what came back would pass on a region that
// was never sealed at all, the design being present in that text for the
// plainest of reasons and no block having been opened to put it there.
std::string EnvelopeUnderNames(const std::string& described) {
  std::string envelope =
      EncryptEnvelopes(Region(described), "", KeysOfBothParties());
  EXPECT_FALSE(Carries(envelope, kSealedDesign));
  return envelope;
}

// The same, for an author who supplied one key of their own. Every region is
// sealed under that key, whoever its lines name, so what an entity is drawn out
// for here is the envelope's own text rather than the choice of a key.
std::string EnvelopeUnderOneKey(const std::string& described) {
  std::string envelope = EncryptEnvelopes(Region(described), kExchangeKey);
  EXPECT_FALSE(Carries(envelope, kSealedDesign));
  return envelope;
}

// `envelope` with `directive` written into it immediately ahead of the
// expression carrying its block. §34.4 gives a value in effect over the text
// after it, so a directive placed here is the one the block is read under
// whatever the envelope stated about itself further up.
std::string EnvelopeReadUnder(const std::string& envelope,
                              const std::string& directive) {
  std::string text = envelope;
  size_t block = text.find(kBlockDirective);
  EXPECT_NE(block, std::string::npos);
  return text.insert(block, directive);
}

// The 1-based line of `envelope` its block is written on, which is the line a
// report about that block stands at. §34.5.15.2 has the directive above it
// indicate that a data block begins on the next line in the file, so the block
// follows that directive by one line (issue #3272).
uint32_t WhereTheNamedBlockIsRead(std::string_view envelope) {
  return LineHolding(envelope, kBlockDirective) + 1;
}

// ---------------------------------------------------------------------------
// The value the line writes against the keyword.
// ---------------------------------------------------------------------------

// The spelling §34.5.10.1 defines: a string written against the keyword. What
// stands in effect afterwards is that string, and it is there because a
// directive put it there rather than because a default did.
TEST(ProtectDataKeyownerSyntax, TheStringAgainstTheKeywordNamesTheEntity) {
  ReadUnderKeys run(Writes("data_keyowner", kOwner));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

// A string is one written thing however much stands between its quotation
// marks, so the two characters that would otherwise break the run up break
// nothing: the comma that separates one expression of a directive from the
// next, and the whitespace that separates one token from the next. Both stand
// inside this name, which is why a legal entity is named the way it is spelled
// rather than the way an identifier would have to be.
//
// A reading that took the comma for the one between two expressions would end
// the name where it is still running and go looking for a keyword in the rest
// of it; one that took the space for the end of a token would leave the word
// after it standing where the directive has nothing further.
TEST(ProtectDataKeyownerSyntax, AnEntityNameHoldingACommaIsOneValue) {
  ReadUnderKeys run(Writes("data_keyowner", "Acme, Incorporated"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "Acme, Incorporated");
}

// The other spelling a string literal has: the form closing on a run of three
// quotation marks rather than on one. It is a string, so it is written where
// the syntax line calls for one, and the name here carries the character that
// form exists for -- a lone quotation mark inside one closes nothing.
//
// What a reading makes of it shows in the expression written after it. A
// reading that ended the value at the lone mark would carry the rest of the
// name into the grammar as tokens the directive never wrote, and the key name
// standing past it would never be reached at all.
TEST(ProtectDataKeyownerSyntax,
     AnEntityNameInTheTripleQuotedSpellingIsOneValue) {
  std::string src = "`pragma protect data_keyowner=";
  src.append("\"\"\"Acme \"the\" Corp\"\"\"");
  src.append(", data_keyname=\"").append(kKeyName).append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyname").value, kKeyName);
}

// The spelling that closes on a single quotation mark, carrying the character
// that would close it behind a backslash. That form has the backslash for
// exactly this, so the two marks in the middle of the name close nothing and
// the value runs to the one at the end.
//
// What the keyword records is the text between the outer marks as the source
// wrote it, backslashes and all. This is a pragma_value rather than a string
// literal of the design being read, so nothing along the way takes a spelling
// back off it.
//
// The key name written after the name is what shows where the value ended. A
// reading that stopped at the first inner mark would carry the rest of the name
// into the grammar as tokens the directive never wrote, and the expression past
// it would never be reached at all.
TEST(ProtectDataKeyownerSyntax, AnEntityNameHoldingAnEscapedQuoteIsOneValue) {
  std::string src = "`pragma protect data_keyowner=\"Acme \\\"the\\\" Corp\"";
  src.append(", data_keyname=\"").append(kKeyName).append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "Acme \\\"the\\\" Corp");
  EXPECT_EQ(run.ValueOf("data_keyname").value, kKeyName);
}

// A string with nothing between its quotation marks is a string, so it is
// written where the syntax line calls for one. What it names is no entity any
// key list is held under, but that is a question about the value rather than
// about the spelling, and a directive carrying it is read like any other.
TEST(ProtectDataKeyownerSyntax, AnEmptyEntityNameIsAString) {
  ReadUnderKeys run(Writes("data_keyowner", ""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "");
}

// §22.5.1 gives a pragma_value more than one spelling, and a keyword recording
// a string is not thereby barred from being written with an identifier against
// it. Both are one written thing, which is what this line calls for, so the
// entity a bare identifier names is the identifier itself -- no quotation marks
// having been written for anything to strip.
TEST(ProtectDataKeyownerSyntax, ABareIdentifierIsOneWrittenThingToo) {
  ReadUnderKeys run(NamesOwner("acme_semiconductor"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme_semiconductor");
}

// The third spelling of one written thing. A number is a pragma_value like the
// other two, and what the keyword records is the value written against it
// rather than the shape that value happened to take, so a party named by a
// number is named.
TEST(ProtectDataKeyownerSyntax, ANumberIsOneWrittenThingToo) {
  ReadUnderKeys run(NamesOwner("1997"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "1997");
}

// The escaped spelling of an identifier, which §5.6.1 runs from its backslash
// to the whitespace ending it. It is an identifier, so it is one written thing
// standing where the syntax line writes one, and the keyword records it with
// the backslash that introduced it -- that being the value as the source wrote
// it, and a value being recorded as written.
//
// It is the one spelling of a single written thing opening on a character no
// other admits. A reading that stepped over the backslash on its own would find
// the letters after it standing as a name in their own right, which would leave
// the expression carrying a keyword where its value belongs.
TEST(ProtectDataKeyownerSyntax, AnEscapedIdentifierIsOneWrittenThingToo) {
  ReadUnderKeys run(NamesOwner("\\acme-semiconductor "));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "\\acme-semiconductor");
}

// ---------------------------------------------------------------------------
// The spelling as a reading meets it.
// ---------------------------------------------------------------------------

// The punctuation with whitespace around it, which is how the syntax line
// itself sets the expression out. Whitespace separates the parts of a directive
// rather than belonging to any of them, so this is the same value.
TEST(ProtectDataKeyownerSyntax, PaddingAroundThePunctuationLeavesTheValue) {
  ReadUnderKeys run("`pragma protect data_keyowner = \"acme-semiconductor\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

// The expression written first on a directive holding a list of expressions,
// with the key name §34.5.12.1 defines after it. The comma that ends this
// expression stands outside the value, so both names come into effect: a
// reading that swallowed the comma would take the designation after it for part
// of the entity's name.
TEST(ProtectDataKeyownerSyntax, TheExpressionFirstInADirectiveListIsRead) {
  std::string src = "`pragma protect data_keyowner=\"";
  src.append(kOwner).append("\", data_keyname=\"").append(kKeyName);
  src.append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
  EXPECT_EQ(run.ValueOf("data_keyname").value, kKeyName);
}

// The same list in the other order. The reading reaches this expression having
// stepped over a value already, which is a different state to carry forward
// than the one the order above leaves it in.
TEST(ProtectDataKeyownerSyntax, TheExpressionLastInADirectiveListIsRead) {
  std::string src = "`pragma protect data_keyname=\"";
  src.append(kKeyName).append("\", data_keyowner=\"").append(kOwner);
  src.append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

// The value need not be written in the source as the value: a directive's text
// is ordinary source text, so a macro usage in it is substituted before the
// pragma grammar reads it. The whole expression arrives that way here, keyword
// and '=' and string alike, so what the grammar reads is text no line of the
// source wrote in that order.
TEST(ProtectDataKeyownerSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  std::string src = "`define WHOSE_KEYS data_keyowner=\"";
  src.append(kOwner).append("\"\n`pragma protect `WHOSE_KEYS\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

// ---------------------------------------------------------------------------
// The string the expression carries is the entity a block is written for.
// ---------------------------------------------------------------------------

// The expression written inside a region the encrypting half is handed. The
// entity it names is combined with the key name beside it to reach one of the
// two keys the tool holds, the region is sealed under that key, and the
// envelope produced states the name in the clear in the spelling the region
// wrote it in.
TEST(ProtectDataKeyownerSyntax, TheEntityARegionNamesReachesItsEnvelope) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  std::string envelope = EnvelopeUnderNames(described);
  EXPECT_TRUE(Carries(envelope, Writes("data_keyowner", kOwner)));
}

// The same envelope handed straight back to a reading holding both parties'
// keys. The pair of names the envelope carries reaches one of them, and the
// design comes back out from under the block.
//
// This is where the string is observed being drawn out of the expression rather
// than merely stepped over: the key name alone stands against a key of each
// party, so the block could only have been sealed and opened under one of the
// two by the entity written beside it.
TEST(ProtectDataKeyownerSyntax, TheEntityAnEnvelopeStatesOpensItsBlock) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeUnderNames(described), f, KeysConfig());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// The negative of that pairing: the same envelope with the other party named
// immediately ahead of its block. The name in effect where a block is read is
// what the block is read under, so the key reached is the other party's -- a
// key the tool really holds and the wrong one -- and the block does not open.
TEST(ProtectDataKeyownerSyntax,
     AnEntityNamedAheadOfABlockIsTheOneItIsReadUnder) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  std::string envelope = EnvelopeReadUnder(
      EnvelopeUnderNames(described), Writes("data_keyowner", kOtherOwner));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, KeysConfig());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      WhereTheNamedBlockIsRead(envelope), "34.3.2"));
  EXPECT_FALSE(Carries(read, "module sealed_m"));
}

// ---------------------------------------------------------------------------
// The list is not the value this keyword is defined with.
// ---------------------------------------------------------------------------

// A parenthesized list of further expressions written against the keyword. The
// syntax line writes a string, which is one written thing, so a list names no
// entity -- and naming none is a different thing from naming an empty one: the
// party named on the line above is still the one the text is read under.
//
// Only a second line shows which of the two a reading does. With one line there
// is no earlier name for a later expression to take away, so a reading that
// wiped the name and a reading that left it alone both end with no party named,
// and neither can be told from the other.
TEST(ProtectDataKeyownerSyntax, AListLeavesTheEntityAlreadyNamedStanding) {
  std::string src = Writes("data_keyowner", kOwner);
  src += NamesOwnerInAList(kOtherOwner);
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

// The same list written into a sealed envelope immediately ahead of its block,
// which is where a name that did settle something would settle what the block
// is opened under. It settles nothing, so the block is read under the party the
// envelope itself states and the design comes back.
//
// The input differs from the one the test above drives in the parentheses and
// the subkeyword alone, so what the reading turned on is the spelling of the
// value rather than the party it spells.
TEST(ProtectDataKeyownerSyntax, AListAheadOfABlockLeavesTheEnvelopesOwnEntity) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  std::string envelope = EnvelopeReadUnder(EnvelopeUnderNames(described),
                                           NamesOwnerInAList(kOtherOwner));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, KeysConfig());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// The list written inside a region the encrypting half is handed, by an author
// holding one key of their own. The region is sealed whatever its lines name,
// so what the list reaches is the envelope's own text -- and it reaches none of
// it: the envelope states no entity, an entity being what §34.5.10 has stated
// in the clear and this line having named none.
//
// A tool that took the list for the name would publish a pragma expression on
// the envelope with somebody's subkeyword list quoted as an entity's name,
// which is why the envelope produced here is read back rather than only looked
// at: the string it would carry holds quotation marks of its own, and the
// directive spelling that puts them inside a string is one no reading recovers.
TEST(ProtectDataKeyownerSyntax, AnEnvelopeStatesNoEntityAListWrote) {
  std::string envelope = EnvelopeUnderOneKey(NamesOwnerInAList(kOtherOwner));
  EXPECT_FALSE(Carries(envelope, "data_keyowner"));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// The pair to it, in the half that chooses a key. A region names its party and
// the key name beside it, and then writes a list against the same keyword. The
// list names nobody, so the party the region did name is the one its key is
// selected through, and the region is sealed rather than left as it was
// written.
//
// A region whose entity a list had wiped would reach no key at all: an entity
// and a key name reach a key together, and neither reaches one alone. That is
// what makes this observable in a text carrying no second party's key -- the
// design is either gone from the output or standing in it.
TEST(ProtectDataKeyownerSyntax, AnEntityNamedBeforeAListStillSelectsTheKey) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  described += NamesOwnerInAList(kOtherOwner);
  std::string envelope = EnvelopeUnderNames(described);
  EXPECT_TRUE(Carries(envelope, Writes("data_keyowner", kOwner)));
}

// ---------------------------------------------------------------------------
// The near misses the reading turns away.
// ---------------------------------------------------------------------------

// The '=' written with nothing after it. The spelling this keyword is defined
// with has a value on the right of it, so a directive that wrote the one
// without the other wrote neither of the two spellings §22.5.1 gives a pragma
// expression.
TEST(ProtectDataKeyownerSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyowner =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The entity's string opened and never closed. This is the closest input to the
// defined spelling the reading has to turn away: everything the syntax line
// writes is on the line, and the one character missing is the mark that ends
// the value.
TEST(ProtectDataKeyownerSyntax, AnUnclosedEntityNameIsNoString) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyowner=\"acme-semiconductor\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

// The parenthesized spelling written empty. That spelling holds a list of
// further expressions rather than an optional one, so an empty pair of
// parentheses is no pragma_value at all, and the author is told rather than
// left with a directive that quietly said nothing.
TEST(ProtectDataKeyownerSyntax, AnEmptyListIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyowner=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The keyword written as an escaped identifier. A pragma_keyword is the simple
// form of an identifier, so the escaped spelling names no keyword at all: it
// stands where the grammar admits a value instead, which leaves the '=' after
// it with nothing on its left that could carry a name.
TEST(ProtectDataKeyownerSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  PreprocFixture f;
  Preprocess("`pragma protect \\data_keyowner = \"acme-semiconductor\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
