// §34.5.9.1 Syntax, for the protect pragma keyword that settles the writing
// every block of an envelope is carried as.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression:
//
//   The keyword is written with an '=' and a value against it, and that value
//   is the parenthesized list of further expressions rather than one written
//   thing. Inside the list stands a scheme, written as a string against the
//   name enctype; it is outside the brackets, so a list is not this value
//   without one. Two further names may follow it, each behind a comma and each
//   carrying a number: a line length, and a count of bytes. They are inside the
//   brackets, so all four combinations of writing them and leaving them out are
//   spellings of this one value, and the order the line writes them in is
//   scheme, length, count.
//
// §22.5.1 gives a pragma_value four spellings -- a number, a string, an
// identifier, and a parenthesized list of pragma expressions -- and this is the
// one keyword of §34.4's table defined with the last of them. That is the whole
// difference between this syntax line and the ones around it: §34.5.8.1 writes
// a keyword whose value is one written thing, and a list of subkeywords written
// against that keyword would be somebody's invention, while here the list is
// what the standard writes and a single word against the keyword is what
// invents something.
//
// The keyword is therefore absent from kStringValuedKeywords in
// src/preprocessor/protect_keywords.cpp. That array names the keywords §34.5
// defines as `keyword = <string>`, and ProtectKeywordScope::Apply records
// nothing for one of them written with a parenthesized value. #3269 is the
// defect that array closes. Adding this keyword to the array would refuse every
// value §34.5.9.1 defines, a list being the only value the keyword is ever
// written with, and
// ProtectEncodingSyntax.TheSchemeNamedInARegionIsTheEnvelopesOwn below is the
// case that would go red on the addition: the envelope that case reads states
// base64 only because the list reached the keyword, and a region whose request
// was dropped is written under the scheme DefaultProtectEncoding in
// src/preprocessor/protect_encoding.cpp supplies instead.
//
// What a reading draws from the expression is real, which is what separates the
// observations below from the ones a keyword nothing is taken from admits. The
// scheme names the writing a block's characters were produced by, so it decides
// whether a block can be read at all; and the count states how much data the
// block stands for, so it decides whether the block standing there is the one
// the envelope describes. Both are therefore visible in what a reading of a
// whole envelope produces, and a length written between them is visible in the
// list still being split where the line writes its commas.
//
// All of it is preprocessor-stage. The reading of the spelling as tokens is the
// pragma grammar in src/preprocessor/preprocessor_lines.cpp, which is where the
// '=' and the parenthesized list are recognized and where the list is carried
// off the directive whole; src/preprocessor/protect_keywords.cpp tabulates the
// name, which is what makes the list a value the protect pragma puts in effect;
// src/preprocessor/protect_encoding.cpp reads that list into the three parts
// this line spells it with and writes one back out in the same shape;
// src/preprocessor/preprocessor_protect_values.cpp is where the parts reach a
// block being opened; and src/preprocessor/protect_region_lines.cpp with
// src/preprocessor/protect_envelope_output.cpp are the encrypting half, which
// takes the scheme a region asked for off the same spelling.
//
// Every input below is written as the real `pragma directive syntax of §22.11.
// §34.5.3.1's and §34.5.4.1's words delimit the envelope the expression really
// stands inside, both as a text writes them by hand and as the encrypting half
// produces them, and §34.5.1.1's and §34.5.2.1's words delimit the region that
// half is handed.

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key an IP author hands the encrypting half, and hands back to a tool
// reading what that half produced. Without one nothing is sealed and nothing is
// opened, so a reading that found no design text could not be told apart from a
// key that was never supplied.
constexpr std::string_view kExchangeKey = "globex-exchange-key";

// The design a region seals. Nothing of it survives the alphabet an encrypted
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The two words §34.5.3.1 and §34.5.4.1 define, as a text carrying a model some
// earlier encryption sealed writes them.
constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

// The directive announcing the block an envelope carries, which §34.5.15.1
// spells as the keyword standing alone. Everything a block is read under has to
// stand ahead of this, so a directive written here is the last word on the
// encoding in effect where the block is opened.
constexpr std::string_view kBlockDirective = "`pragma protect data_block\n";

// One of the two schemes Table 34-2 requires of every implementation, and the
// one this tool can carry a block under as the value of the expression naming
// it. A region asking for it therefore gets it, which is what makes a scheme
// named in the input visible in the envelope produced from it.
constexpr std::string_view kNamedScheme = "base64";

// Whether `text` writes `written` anywhere in it.
bool Carries(std::string_view text, std::string_view written) {
  return text.find(written) != std::string_view::npos;
}

// The directive this subclause defines, carrying `list` as the pragma_value
// written against the keyword. The list is passed in whole, parentheses and
// all, because which characters stand there is the thing being observed.
std::string StatesEncoding(std::string_view list) {
  std::string directive = "`pragma protect encoding=";
  directive.append(list).append("\n");
  return directive;
}

// The value in the shape the syntax line writes it: the scheme written as a
// string against the name that requires one, and `after` standing where the two
// optional names go, comma and all, with the parenthesis that closes the list
// left to this helper.
std::string EncodingList(std::string_view enctype, std::string_view after) {
  std::string list = "(enctype=\"";
  list.append(enctype).append("\"").append(after).append(")");
  return list;
}

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with `inside`
// between them and the design after it. The design comes last so that a line
// the encryption passed over is a line that went into the block ahead of it.
std::string RegionHolding(std::string_view inside) {
  std::string region = "`pragma protect begin\n";
  region.append(inside).append(kSealedDesign);
  region.append("`pragma protect end\n");
  return region;
}

// What a reading is configured with for opening the protected regions an input
// carries, which is the key and nothing besides.
PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  return config;
}

// The envelope the encrypting half leaves where a region holding `inside` was
// written, checked on the way out to be one: the design it was formed from is
// gone from the text.
//
// A round trip that looked only at what came back would pass on a region that
// was never sealed at all, the design being present in that text for the
// plainest of reasons and no block having been opened to put it there.
std::string EnvelopeAround(std::string_view inside) {
  std::string envelope = EncryptEnvelopes(RegionHolding(inside), kExchangeKey);
  EXPECT_FALSE(Carries(envelope, kSealedDesign));
  return envelope;
}

// The same envelope with `directive` written into it immediately ahead of the
// expression carrying its block. §34.4 has a value in effect over the text
// after it, so a directive placed here is the one the block is read under
// whatever the envelope stated about itself further up.
std::string EnvelopeReadUnder(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t block = envelope.find(kBlockDirective);
  EXPECT_NE(block, std::string::npos);
  return envelope.insert(block, std::string(directive));
}

// The 1-based line of `envelope` its block is written on, which is the line a
// report about that block stands at. §34.5.15.2 has the directive above it
// indicate that a data block begins on the next line in the file, so the block
// is one line past that directive (issue #3272).
uint32_t WhereTheEncodedBlockStands(std::string_view envelope) {
  return LineHolding(envelope, kBlockDirective) + 1;
}

// ---------------------------------------------------------------------------
// The four spellings the brackets admit.
// ---------------------------------------------------------------------------

// The whole line as it is written, with both optional names present: a scheme,
// a length behind a comma, a count behind another. This is the one input
// carrying every part of the syntax line at once, and the reading consumes the
// directive on it without any of the list reaching the design text.
TEST(ProtectEncodingSyntax, TheListWithBothOptionalNamesIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(
      EncodingList(kNamedScheme, ", line_length=64, bytes=128")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_FALSE(Carries(read, kNamedScheme));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

// The list with neither optional name, which is the shortest value this keyword
// is defined with: the brackets are what say the two may be left out, and the
// scheme standing outside them is what says something has to be written.
TEST(ProtectEncodingSyntax, TheListNamingOnlyASchemeIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(EncodingList("uuencode", "")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "uuencode"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// The first bracket written and the second left out. The two are separate
// brackets rather than one, so a value taking the earlier option without the
// later one is a value the line writes.
TEST(ProtectEncodingSyntax, TheListWithALengthAndNoCountIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(EncodingList(kNamedScheme, ", line_length=72")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "line_length"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// The mirror image: the later bracket taken and the earlier one left out, which
// with the three above exhausts the four combinations the two brackets admit. A
// reading that had taken the second option to depend on the first would find a
// count where it was looking for a length.
TEST(ProtectEncodingSyntax, TheListWithACountAndNoLengthIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(EncodingList(kNamedScheme, ", bytes=256")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "bytes"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// ---------------------------------------------------------------------------
// The spelling as a reading meets it.
// ---------------------------------------------------------------------------

// The punctuation with whitespace around every piece of it, which is how the
// syntax line itself sets the value out. Whitespace separates the parts of a
// directive rather than belonging to any of them, so this is the same value.
TEST(ProtectEncodingSyntax, PaddingAroundThePunctuationLeavesTheValue) {
  PreprocFixture f;
  std::string src = "`pragma protect encoding = ( enctype = \"base64\" , ";
  src.append("line_length = 64 , bytes = 128 )\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "enctype"));
}

// The expression written first on a directive holding a list of expressions,
// with another after it. The value is itself a list, so the comma that ends it
// stands outside the parentheses while the commas inside them are the value's
// own: a reading that did not tell the two apart would take the expression
// after this one for a further subkeyword of the scheme.
TEST(ProtectEncodingSyntax, TheExpressionFirstInADirectiveListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect encoding=";
  src.append(EncodingList(kNamedScheme, ", bytes=128"));
  src.append(", comment=\"rev 3\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "rev 3"));
  EXPECT_FALSE(Carries(read, kNamedScheme));
}

// The same list in the other order. The reading reaches this expression having
// stepped over a value already, which is a different state to carry forward
// than the one the order above leaves it in.
TEST(ProtectEncodingSyntax, TheExpressionLastInADirectiveListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect comment=\"rev 3\", encoding=";
  src.append(EncodingList(kNamedScheme, ", line_length=64")).append("\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kNamedScheme));
}

// The expression standing inside the envelope §34.5.3.1's and §34.5.4.1's words
// delimit, with those words written as source text rather than produced by the
// encrypting half. That is the position the definition is really for: an
// envelope somebody else sealed, whose expressions stand in whatever order its
// producer wrote them, met by a tool that had no hand in writing it.
TEST(ProtectEncodingSyntax, TheExpressionInsideASealedModelIsRead) {
  PreprocFixture f;
  std::string sealed(kBeginProtected);
  sealed.append(StatesEncoding(EncodingList(kNamedScheme, ", bytes=128")));
  sealed.append(kEndProtected);
  std::string read = Preprocess("module m;\n" + sealed + "endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kNamedScheme));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

// The value need not be written in the source as the value: a directive's text
// is ordinary source text, so a macro usage in it is substituted before the
// pragma grammar reads it. The whole of the list arrives that way here,
// parentheses and commas and all, so what the grammar reads as the
// parenthesized value is text no line of the source wrote in that order.
TEST(ProtectEncodingSyntax, AMacroExpandingToTheWholeListIsRead) {
  PreprocFixture f;
  std::string src = "`define HOW_WRITTEN encoding=";
  src.append(EncodingList(kNamedScheme, ", line_length=64, bytes=128"));
  src.append("\n`pragma protect `HOW_WRITTEN\nmodule m;\nendmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kNamedScheme));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// ---------------------------------------------------------------------------
// What the scheme's string admits.
// ---------------------------------------------------------------------------

// A string is one written thing however much punctuation stands inside it, so a
// comma between the quotation marks separates nothing. A reading that took it
// for the comma between two subkeyword expressions would end the scheme where
// its name is still running and go looking for a subkeyword in the rest of it.
TEST(ProtectEncodingSyntax, ASchemeNameHoldingACommaIsOneValue) {
  PreprocFixture f;
  std::string read =
      Preprocess(StatesEncoding("(enctype=\"x-acme,scheme\")"), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "x-acme"));
}

// The same for the character that closes the list. A reading that looked for it
// before it looked for the closing quotation mark would end the value inside
// the scheme's name and be left with the rest of the string standing where the
// directive has nothing further.
TEST(ProtectEncodingSyntax, ASchemeNameHoldingACloseParenIsOneValue) {
  PreprocFixture f;
  std::string read =
      Preprocess(StatesEncoding("(enctype=\"x-acme)scheme\")"), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "x-acme"));
}

// The other spelling a string literal has: the form closing on a run of three
// quotation marks rather than on one. It is a string, so it is written where
// the syntax line calls for one, and the name here carries the character that
// form exists for -- a lone quotation mark inside one closes nothing.
//
// Written without that character the name would be read the same way whichever
// mark the form was thought to close on, and the spelling would go unobserved.
// With it, a reading that ended the value at the lone mark would carry the rest
// of the name into the grammar as tokens the directive never wrote, and the
// list would close on nothing.
TEST(ProtectEncodingSyntax, ASchemeNameInTheTripleQuotedSpellingIsOneValue) {
  PreprocFixture f;
  std::string read =
      Preprocess(StatesEncoding("(enctype=\"\"\"x-acme\"scheme\"\"\")"), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "x-acme"));
}

// A string with nothing between its quotation marks is a string, so it is
// written where the syntax line calls for one. What it names is no scheme, but
// that is a question about the value rather than about the spelling, and the
// directive carrying it is consumed like any other.
TEST(ProtectEncodingSyntax, AnEmptySchemeNameIsAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding("(enctype=\"\")")).append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// ---------------------------------------------------------------------------
// The scheme the list names is the writing the blocks are produced by.
// ---------------------------------------------------------------------------

// The expression written inside a region the encrypting half is handed, driven
// through both halves in turn. The scheme the list names is the one the
// envelope produced from that region states for itself, and the envelope is
// handed straight back to a reading holding the author's key, which recovers
// the design from under a block written in that scheme.
//
// This is where the string against enctype is observed being drawn out of the
// expression rather than merely stepped over: nothing else in the input names a
// scheme, so the envelope could not state this one had the list not been read.
TEST(ProtectEncodingSyntax, TheSchemeNamedInARegionIsTheEnvelopesOwn) {
  std::string envelope =
      EnvelopeAround(StatesEncoding(EncodingList(kNamedScheme, "")));
  ASSERT_TRUE(Carries(envelope, "enctype=\"base64\""));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// A region naming a scheme on one line and writing a value that names none on
// the next. The second value is not this keyword's -- the scheme stands outside
// the brackets that make the other two names optional -- so it settles nothing,
// and the envelope is written under the scheme the region did name.
//
// Settling nothing is a different thing from settling emptiness, and only a
// second line shows which of the two a reading does. With one line there is no
// earlier request for a later expression to take away, so a reading that wiped
// the request and a reading that left it alone both end at the scheme this tool
// writes its own blocks under, and neither can be told from the other.
TEST(ProtectEncodingSyntax, AValueNamingNoSchemeLeavesTheOneAlreadyNamed) {
  std::string inside(StatesEncoding(EncodingList(kNamedScheme, "")));
  inside.append(StatesEncoding("(bytes=190)"));
  std::string envelope = EnvelopeAround(inside);
  ASSERT_TRUE(Carries(envelope, "enctype=\"base64\""));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// The same region with the scheme's name written as a bare word instead of a
// string. §34.5.9.1 writes a string there, and §22.5.1 spells an identifier as
// something else again, so the letters standing between the '=' and the comma
// name no scheme however much they look like one -- and the envelope produced
// states the writing this tool uses where a text asked for nothing.
//
// This is the sharpest negative of the scheme's spelling: every character the
// syntax line calls for is on the line and in its order, and the two marks that
// make the word a string are missing. It stands for every non-string spelling
// rather than one of them: the reading asks whether the value opens and closes
// on a quotation mark, so a number written here is turned away at the same
// character as this word and by the same comparison.
TEST(ProtectEncodingSyntax, ASchemeWrittenAsABareWordNamesNothing) {
  std::string envelope = EnvelopeAround(StatesEncoding("(enctype=base64)"));
  EXPECT_FALSE(Carries(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Carries(envelope, "enctype=\""));
}

// A single written thing against the keyword, which is a pragma_value §22.5.1
// admits and is not the one this keyword is defined with. The letters of a
// scheme's name are all there, and what is missing is the list they would have
// had to stand inside as the value of a subkeyword, so the region asked for no
// scheme and its envelope states the writing this tool uses.
//
// The string is written here on behalf of all three single written things
// §22.5.1 spells. Which of them a value was is settled by the pragma grammar
// and gone by the time this keyword's value is read: what reaches the reading
// is the text of one token, and a run of characters holding no '=' names no
// subkeyword whether it was a string, a number or an identifier. The string is
// the one worth writing because it is the near miss a producer would make --
// the scheme's name, correctly quoted, one pair of parentheses short.
TEST(ProtectEncodingSyntax, AStringAgainstTheKeywordNamesNoScheme) {
  std::string envelope =
      EnvelopeAround("`pragma protect encoding=\"base64\"\n");
  EXPECT_FALSE(Carries(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Carries(envelope, "enctype=\""));
}

// ---------------------------------------------------------------------------
// The count the list states is measured against the block.
// ---------------------------------------------------------------------------

// The round trip with nothing stated in the region at all. What the encrypting
// half writes into the envelope is this very expression -- the scheme it wrote
// the block under, and against the bytes name the count of what the block
// stands for -- so the shape the syntax line defines is what a reading is
// handed, and the block opens against it.
TEST(ProtectEncodingSyntax, TheCountAnEnvelopeStatesFitsItsOwnBlock) {
  std::string envelope = EnvelopeAround("");
  ASSERT_TRUE(Carries(envelope, "bytes="));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// The same envelope with a count that its block does not hold, written in the
// defined shape immediately ahead of the block. The number against the bytes
// name is read as a number and measured against what the block recovered to, so
// a block of another size is reported rather than tried against a key.
TEST(ProtectEncodingSyntax, ACountDisagreeingWithTheBlockIsReported) {
  std::string list =
      EncodingList(DefaultProtectEncoding().enctype, ", bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

// The same disagreeing count with a length written between it and the scheme,
// which is the order the syntax line puts the three names in. The count is
// still found and still measured, so the length occupied one element of the
// list and swallowed neither of its neighbours -- which is the whole of what
// the comma before it and the comma after it are for.
TEST(ProtectEncodingSyntax, ALengthBetweenTheSchemeAndCountLeavesBoth) {
  std::string list = EncodingList(DefaultProtectEncoding().enctype,
                                  ", line_length=8, bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

// The same input with the length written as a string. §34.5.9.1 writes a
// number against this name as it does against the count, so what stands here is
// no length.
//
// What a reading can be seen to make of that is what the list beyond it still
// does. A length a text states is carried nowhere a reader can see it: it says
// how a block about to be written is to be broken into lines, and a block
// already written was broken by whoever wrote it, so taking the value and
// dropping it leave the same text behind. What would show is a reading that
// made something of the wrong sort of value -- and the count past this element
// is still found and still measured, so the malformed element took nothing from
// its neighbour and stopped no part of the list from being read.
//
// The input differs from the one above in the two quotation marks alone.
TEST(ProtectEncodingSyntax, ALengthWrittenAsAStringLeavesTheCountBeyondIt) {
  std::string list = EncodingList(DefaultProtectEncoding().enctype,
                                  ", line_length=\"wide\", bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

// The three names written in the reverse of the order the syntax line puts them
// in. The count is still found and still measured against the block, so every
// element was read for the name it carries rather than for the position it
// stands in.
//
// That is what a reader owes a producer it never met. The syntax line settles
// what a tool writes, and §34.5.3's envelope is one somebody else sealed, whose
// expressions stand in whatever order that producer wrote them. A reading that
// dropped a scheme for standing last would open the block under a writing its
// producer never named and lose the design, which says nothing about the order
// to anybody -- so accepting more here than the line writes costs nothing,
// every element of this value naming itself.
TEST(ProtectEncodingSyntax, TheNamesAreReadForThemselvesWhateverTheOrder) {
  std::string list = "(bytes=1, line_length=8, enctype=\"";
  list.append(DefaultProtectEncoding().enctype).append("\")");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

// The same disagreeing count written as a string rather than as a number.
// §34.5.9.1 writes a number against the bytes name, so a word standing there is
// no count at all: nothing is measured against the block, and the envelope is
// read exactly as one stating no count is.
//
// The input differs from the one ACountDisagreeingWithTheBlockIsReported drives
// in the two quotation marks alone, so what the reading turned on is the sort
// of thing the value is.
//
// It is the string rather than any other non-number spelling because the count
// is read character by character and gives up at the first that is no digit.
// A word holding no digit at all would be turned away by that same comparison
// on its first character; this one holds a digit the reading has to decline to
// go looking for.
TEST(ProtectEncodingSyntax, ACountWrittenAsAStringIsNoCount) {
  std::string list =
      EncodingList(DefaultProtectEncoding().enctype, ", bytes=\"1\"");
  PreprocFixture f;
  std::string read =
      Preprocess(EnvelopeReadUnder(StatesEncoding(list)), f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// The same disagreeing count in a list that names no scheme. The scheme is the
// one name §34.5.9.1 writes outside the brackets, so a list without it is not
// the value this keyword is defined with, and the count written inside it
// describes a block under no scheme at all. Nothing is measured against the
// block, and the envelope is read exactly as one stating no count is.
//
// The input differs from the one ACountDisagreeingWithTheBlockIsReported drives
// in the scheme alone, so what the reading turned on is the name the syntax
// line requires.
TEST(ProtectEncodingSyntax, ACountInAListNamingNoSchemeStatesNothing) {
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeReadUnder(StatesEncoding("(bytes=1)")),
                                f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// ---------------------------------------------------------------------------
// The near misses the reading turns away.
// ---------------------------------------------------------------------------

// The other spelling §22.5.1 gives a pragma expression: the keyword standing
// alone. This subclause defines it with a value against it, so a directive
// writing it this way states no scheme -- and the block of the envelope it
// stands in is opened under the writing this tool uses, which is what a text
// stating nothing is read under.
TEST(ProtectEncodingSyntax, TheKeywordStandingAloneStatesNoScheme) {
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeReadUnder("`pragma protect encoding\n"),
                                f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

// The parenthesized spelling written empty. That spelling holds a list of
// further expressions rather than an optional one, so an empty pair of
// parentheses is no pragma_value at all, and the author is told rather than
// left with a directive that quietly said nothing.
TEST(ProtectEncodingSyntax, AnEmptyListIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The '=' written with nothing after it. The spelling this keyword is defined
// with has a value on the right of it, so a directive that wrote the one
// without the other wrote neither of the two spellings §22.5.1 gives a pragma
// expression.
TEST(ProtectEncodingSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// A list opened and never closed. This is the closest input to the defined
// spelling the reading has to turn away: everything the syntax line writes is
// on the line, and the one character missing is the one that ends the list.
TEST(ProtectEncodingSyntax, AListLeftUnclosedIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding=(enctype=\"base64\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The scheme's string opened and never closed. The mark that would have ended
// it is the one closing the list instead, so the value runs to the end of the
// line with neither of the two things it opened ever finished.
TEST(ProtectEncodingSyntax, AnUnclosedSchemeNameIsNoString) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding=(enctype=\"base64)\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

// A subkeyword written with no '=' and no value, inside a list that is
// otherwise the one the syntax line defines. Every element of this value is a
// name bound to something, so a bare word standing among them is a pragma
// expression the grammar admits in a position this keyword's value has no
// element for -- and it is the reading of the list that has to keep the scheme
// it stands beside from being lost with it.
TEST(ProtectEncodingSyntax, ABareWordAmongTheSubkeywordsQualifiesNothing) {
  std::string list =
      EncodingList(DefaultProtectEncoding().enctype, ", padded, bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

// The keyword written as an escaped identifier. A pragma_keyword is the simple
// form of an identifier, so the escaped spelling names no keyword at all: it
// stands where the grammar admits a value instead, which leaves the '=' after
// it with nothing on its left that could carry a list.
TEST(ProtectEncodingSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  PreprocFixture f;
  Preprocess("`pragma protect \\encoding = (enctype = \"base64\")\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
