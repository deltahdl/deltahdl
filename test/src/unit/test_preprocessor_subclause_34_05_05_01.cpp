// §34.5.5.1 Syntax, for the protect pragma keyword that names who wrote the IP
// an envelope carries.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression:
//
//   The keyword is written with an '=' and a string against it.
//
// §22.5.1 offers a pragma expression two spellings -- a pragma_keyword standing
// alone, and a pragma_keyword with a pragma_value written against it -- and the
// words delimiting an envelope are defined with the first of them. This one is
// defined with the second, and the syntax line goes further than choosing
// between the two: it writes what stands on the right of the '=' as a string,
// which is one written thing rather than a list of things. §22.5.1 spells a
// pragma_value the other way as well, as a parenthesized list of further
// expressions naming the parts of a value, and §34.5.9.1 is where a keyword of
// this same table is defined with one. A list written here is therefore a
// spelling belonging to some other keyword's definition rather than to this
// one, and what it holds is somebody's subkeywords rather than a person's name.
//
// What turns on the spelling is which line of an author's own source text is
// read as saying who they are. The expression is the one thing §34.5.5 has an
// encrypting tool lift out of the text it is about to seal and write in the
// clear on the envelope instead, so the spelling decides two things at once: a
// line taken for it is published rather than encrypted, and a line passed over
// leaves the envelope saying nothing about whose design it carries. Both
// failures are silent in the produced text unless the block is opened, which is
// why the readings below open it rather than only looking at what stands
// outside.
//
// All of it is preprocessor-stage. src/preprocessor/protect_keywords.h holds
// the name, and src/preprocessor/protect_pragma_line.cpp holds the reading of a
// line that decides which keyword a directive named and what was written
// against it. The half that acts on the answer asks twice over every line an
// encryption envelope encloses: src/preprocessor/protect_processing.cpp holds
// the line back from the block and
// src/preprocessor/protect_region_lines.cpp takes the name for the envelope.
// src/preprocessor/protect_envelope_output.cpp writes the expression back out
// through src/preprocessor/protect_keywords.cpp. The reading half meets the
// same directive as tokens instead, through the pragma grammar in
// src/preprocessor/preprocessor_lines.cpp.
//
// Every input below is written as the real `pragma directive syntax of §22.11.
// The region whose author is being named is delimited by §34.5.1.1's and
// §34.5.2.1's words; §34.5.10.1's and §34.5.12.1's expressions name the entity
// that provided the key and the key of theirs the region is under, so a region
// that came back encrypted came back encrypted because those names really
// reached a key; §34.5.3.1's and §34.5.4.1's words delimit a model an earlier
// encryption sealed already; and §34.5.9.1's parenthesized value is the real
// syntax the list form is written from.
//
// The value the keyword records is read back off the preprocessor as well as
// looked for in the produced text. A list written against the keyword records
// no name, so a name an earlier directive wrote still stands and a keyword no
// directive named stands at its default. #3269 is the defect those two
// readings close: the parentheses and the subkeywords of a list were recorded
// as the author §34.5.5.1 defines the keyword to name.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_region.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The name a region writes against the keyword, and the directive an envelope
// carries it on. The name holds a space, so it can only have reached the output
// as the value of an expression rather than as a stray word of the source.
constexpr std::string_view kAuthorName = "Ada Lovelace";
constexpr std::string_view kAuthorDirective =
    "`pragma protect author=\"Ada Lovelace\"\n";

// The opening of any such directive, for the readings that ask whether an
// envelope names an author at all rather than which one.
constexpr std::string_view kAnyAuthorDirective = "`pragma protect author=";

// The parenthesized spelling §22.5.1 gives a pragma_value, written against this
// keyword: a list of further expressions, whose subkeywords are somebody's own
// devising. It is the sharpest near miss the defined value has, every letter of
// the name being on the line and in its order.
constexpr std::string_view kListAgainstTheKeyword =
    "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n";

// The text standing where a region writing `written` inside itself was, for a
// tool holding that region's key.
std::string EncryptedRegionWriting(std::string_view written) {
  return Encrypted(RegionWriting(written));
}

// A source text read through the preprocessor by a tool holding the region
// keys, with the text the reading produced and the diagnostics it raised.
struct ReadSource {
  static PreprocConfig KeyConfig() {
    PreprocConfig config;
    config.protect_keys = TheRegionsKey();
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit ReadSource(const std::string& src) {
    Preprocessor pp(mgr, diag, KeyConfig());
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// ---------------------------------------------------------------------------
// The keyword, an '=', and a string.
// ---------------------------------------------------------------------------

// The syntax line read at its plainest: the keyword with a string written
// against it is the expression, so the name that string carries is the name the
// envelope taking the region's place carries, and the design the region held is
// sealed rather than standing in the clear beside it.
TEST(ProtectAuthorSyntax, TheKeywordWithAStringNamesTheAuthor) {
  std::string written = EncryptedRegionWriting(kAuthorDirective);
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

// The other half of what the spelling settles, read out of the block itself:
// the line carrying the expression was held back from the text the block
// records, which is what leaves the name readable without the key. The design
// written beside it went in, so the block is the block of this region.
TEST(ProtectAuthorSyntax, TheKeywordWithAStringIsHeldBackFromTheBlock) {
  std::string opened = OpenedBlockWriting(kAuthorDirective);
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyAuthorDirective));
}

// The '=' with whitespace on either side of it, which is how the syntax line
// itself writes the expression. Whitespace separates the parts of a directive
// rather than belonging to any of them, so this is the same expression and
// carries the same name.
TEST(ProtectAuthorSyntax, PaddingAroundTheEqualsLeavesTheExpressionStanding) {
  std::string written =
      EncryptedRegionWriting("`pragma  protect  author  =  \"Ada Lovelace\"\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

// The expression written on a directive holding a list, ahead of another
// expression. Each expression of a list is spelled on its own, so a comma after
// the string ends this expression and the one after it says nothing about the
// name.
TEST(ProtectAuthorSyntax, TheExpressionFirstInAListStillNamesTheAuthor) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect author=\"Ada Lovelace\", comment=\"rev 3\"\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

// The same list in the other order. The reading reaches this expression having
// stepped over a string already, which is a different state to carry forward
// than the one the order above leaves it in.
TEST(ProtectAuthorSyntax, TheExpressionLastInAListStillNamesTheAuthor) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect comment=\"rev 3\", author=\"Ada Lovelace\"\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

// A comment is not a pragma expression, so a directive whose expression is
// followed by one wrote the expression and nothing else. Without this the
// string would have to be the last thing on its line to be the string.
TEST(ProtectAuthorSyntax, ACommentAfterTheStringLeavesTheExpressionStanding) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect author=\"Ada Lovelace\" // who wrote this\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

// ---------------------------------------------------------------------------
// What a string admits.
// ---------------------------------------------------------------------------

// A string is one written thing however much punctuation stands inside it, so a
// comma written between the quotation marks separates nothing: the name is the
// whole of what the quotation marks enclose rather than the part of it standing
// ahead of the comma.
TEST(ProtectAuthorSyntax, AStringHoldingACommaIsOneName) {
  std::string naming = "`pragma protect author=\"Lovelace, Ada\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
}

// The same for the punctuation that opens a comment. A reading that looked for
// it before it looked for the closing quotation mark would end the expression
// inside the name and publish half of it.
TEST(ProtectAuthorSyntax, AStringHoldingCommentPunctuationIsOneName) {
  std::string naming =
      "`pragma protect author=\"Ada Lovelace // Analytical Engine\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
}

// The same for a string that writes this very expression inside itself. The
// letters between the quotation marks name nothing: they are characters of one
// keyword's value, and the expression the directive wrote is the one whose
// keyword stands outside the quotation marks.
TEST(ProtectAuthorSyntax, AStringHoldingTheExpressionIsOneName) {
  std::string naming = "`pragma protect author=\"author=Ada Lovelace\"\n";
  std::string written = EncryptedRegionWriting(naming);
  EXPECT_TRUE(Holds(written, naming));
  EXPECT_EQ(TimesWritten(written, kAnyAuthorDirective), 1U);
}

// A quotation mark written behind a backslash is content of the string rather
// than the end of it, so a name written with one inside is still one string and
// still one name. A reading that ended the string at the first such mark would
// carry a fragment of the name onto the envelope and leave the rest of the line
// unaccounted for.
TEST(ProtectAuthorSyntax, AStringHoldingAnEscapedQuoteIsOneName) {
  std::string naming =
      "`pragma protect author=\"Ada \\\"the Countess\\\" Lovelace\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
}

// A string with nothing between its quotation marks is a string, so the
// expression is the expression and the line carrying it is the naming rather
// than text of the design. What it names is a design whose author is written as
// nobody, which is the author this region stated.
TEST(ProtectAuthorSyntax, AnEmptyStringIsAString) {
  std::string naming = "`pragma protect author=\"\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
  EXPECT_FALSE(Holds(OpenedBlockWriting(naming), kAnyAuthorDirective));
}

// ---------------------------------------------------------------------------
// The spellings this expression is not defined with.
// ---------------------------------------------------------------------------

// The first of the two spellings §22.5.1 gives a pragma expression, which this
// keyword is not defined with: the keyword standing alone writes no string, so
// it names nobody and the envelope has no name to carry.
TEST(ProtectAuthorSyntax, TheKeywordStandingAloneWritesNoString) {
  std::string written = EncryptedRegionWriting("`pragma protect author\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// Where that line went instead, which the produced text cannot show: naming
// nobody, it is not the expression §34.5.5 lifts out of the region, so §34.5.1
// governs the rest of the enclosed text and this line is sealed with it.
//
// The reading that holds a line back from the block and the reading that takes
// the name for the envelope have to turn this spelling away alike. One that
// held it back on account of a name the other never took would lose the line in
// both directions at once.
TEST(ProtectAuthorSyntax, TheKeywordStandingAloneIsSealed) {
  std::string bare = "`pragma protect author\n";
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

// The other pragma_value spelling §22.5.1 admits, and the closest input this
// rule has to turn away: a parenthesized list of further expressions written
// where the string belongs. A list is not one written thing, so it is not the
// value this keyword is defined with, and what it holds are subkeywords of
// somebody's own devising rather than a person's name.
//
// A reading that took it would publish that list on the envelope in the clear
// as the name of whoever wrote the design.
TEST(ProtectAuthorSyntax, AParenthesizedListAgainstTheKeywordNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// The other half of the same rule, which no absence from the produced text can
// show: naming nobody, the line is not the one expression §34.5.5 lifts out of
// the region, so §34.5.1's rule for the rest of the enclosed text governs and
// it goes into the block along with the design.
//
// The two halves have to answer alike. A line held back from the block on
// account of a name that never reached the envelope would be lost in both
// directions at once -- neither sealed with the design nor written in the
// clear.
TEST(ProtectAuthorSyntax, AParenthesizedListAgainstTheKeywordIsSealed) {
  std::string listed =
      "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n";
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

// ---------------------------------------------------------------------------
// What a list leaves the keyword recording.
// ---------------------------------------------------------------------------

// The two readings above ask what the encrypting half publishes, which is
// nothing either way. What a reading records for the keyword is a separate
// answer, and it is read off the preprocessor once the whole text has passed
// through: it belongs to the point the reading has reached rather than to any
// one line of output.

// A list written against the keyword on a text that already named an author.
// The list names nobody, and naming nobody is not naming an empty author, so
// the name the earlier directive wrote is still the name the keyword records.
//
// Only the earlier directive tells the two apart. With the list standing alone
// there is no name for it to take away, so a reading that wiped the name and a
// reading that let it stand both end with no name recorded. #3269 is the defect
// this closes: the list was recorded as the author, punctuation and subkeywords
// and all.
TEST(ProtectAuthorSyntax, AListLeavesTheAuthorAlreadyNamedStanding) {
  std::string src(kAuthorDirective);
  src += kListAgainstTheKeyword;
  ReadWithTheKeys run(src);
  EXPECT_FALSE(run.diags.HasErrors());
  EXPECT_FALSE(run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).defaulted);
  EXPECT_EQ(run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).value,
            kAuthorName);
}

// The same list on a text no directive named an author in. It names nobody, so
// the keyword stands at the default ProtectKeywordScope::ValueOf in
// src/preprocessor/protect_keywords.cpp gives a keyword no directive wrote: the
// empty string, reported as defaulted.
//
// That is what makes the case above about the spelling of the value rather than
// about the name that happened to stand ahead of it.
TEST(ProtectAuthorSyntax, AListWithNoAuthorNamedBeforeItLeavesTheDefault) {
  ReadWithTheKeys run{std::string(kListAgainstTheKeyword)};
  EXPECT_FALSE(run.diags.HasErrors());
  EXPECT_TRUE(run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).defaulted);
  EXPECT_TRUE(
      run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).value.empty());
}

// ---------------------------------------------------------------------------
// Names that are not this name.
// ---------------------------------------------------------------------------

// SystemVerilog distinguishes case, so the letters written in another case name
// a keyword this specification sets nothing aside for, and a string written
// against it names nobody.
TEST(ProtectAuthorSyntax, TheLettersInAnotherCaseAreNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect AUTHOR=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// A pragma_keyword is a simple identifier, so the same letters written as an
// escaped identifier name something else. A reading that stepped over the
// backslash alone would find this keyword standing where the directive grammar
// finds one token that is no keyword at all.
TEST(ProtectAuthorSyntax, TheLettersAsAnEscapedIdentifierAreNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect \\author =\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// A longer name this one's whole spelling opens is a name of its own, and this
// table sets one aside: the keyword §34.5.6 defines carries whatever further
// documentation a design offers about its author, which is not the author's
// name. A reading that compared only as far as this keyword's own length would
// take that documentation for the name.
TEST(ProtectAuthorSyntax, ALongerTabulatedNameIsNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect author_info=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// The letters standing on the right of an '=' are the pragma_value of the
// keyword written on its left rather than a pragma_keyword of the list, so they
// name no expression of the directive. The reading has to carry the fact of the
// '=' across to the letters after it; one that forgot would find this keyword
// here.
TEST(ProtectAuthorSyntax, TheLettersWrittenAsAValueAreNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect comment=author\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// A pragma_value may itself be a list of pragma expressions, and an expression
// written inside one belongs to that list rather than to the directive's own.
// It qualifies the value of the keyword carrying it, so it names no author --
// the same conclusion as the letters standing on the right of an '=', reached
// over a different spelling.
TEST(ProtectAuthorSyntax, TheExpressionInsideAParenthesizedValueNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect encoding=(enctype=\"base64\", "
      "author=\"Ada Lovelace\")\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// The whole expression written inside a string is characters of that string.
// The keyword carrying it is the one standing outside the quotation marks, and
// this directive wrote no author expression at all.
TEST(ProtectAuthorSyntax, TheExpressionInsideAStringNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect comment=\"author=\\\"Ada Lovelace\\\"\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// A comment is not part of the expression list at all, so an expression written
// after one on the same line was not written on the list. The letters are there
// in the line for a reading to find, which is what makes this the pair to the
// comment written after a real expression above.
TEST(ProtectAuthorSyntax, TheExpressionAfterACommentNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect comment=\"rev 3\" // author=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// The keyword belongs to the protect pragma, which is the specification the
// pragma_name selects. Written under another pragma_name it asks a
// specification this implementation does not recognize for something, and the
// envelopes of the text are left alone.
TEST(ProtectAuthorSyntax, TheKeywordUnderAnotherPragmaNameNamesNobody) {
  std::string written =
      EncryptedRegionWriting("`pragma acme author=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// The other position on a directive of this shape: the pragma_name itself.
// There the letters name a specification rather than asking one for something,
// and the specification they name is not the one protected envelopes belong to.
TEST(ProtectAuthorSyntax, TheKeywordAsThePragmaNameNamesNobody) {
  std::string written =
      EncryptedRegionWriting("`pragma author = \"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

// ---------------------------------------------------------------------------
// The same spelling met by the reading half.
// ---------------------------------------------------------------------------

// The directive as a tool reading source text meets it, which is as tokens of
// the pragma grammar rather than as characters of a line. The expression is one
// the grammar accepts, the directive is consumed like any other, and the name
// reaches none of the text the compilation step after the preprocessor reads.
TEST(ProtectAuthorSyntax, TheDirectiveCarryingTheExpressionContributesNoText) {
  ReadSource read("module m;\n" + std::string(kAuthorDirective) +
                  "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

// The expression need not be written in the source as the expression: a
// directive's text is ordinary source text, so a macro usage in it is
// substituted before the pragma grammar reads it. The whole of the expression
// arrives that way here, punctuation and all, so what the grammar reads as the
// keyword, the '=' and the string is text no line of the source wrote in that
// order.
//
// The substitution is one call over the directive's whole text rather than one
// per position, so a usage standing where the value belongs reaches the grammar
// by the very path this one does. A directive the substitution had not reached
// would still carry the macro's own punctuation, which is no token of this
// grammar, so the reading coming away with nothing to report is the
// substitution having happened first.
TEST(ProtectAuthorSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  ReadSource read(
      "`define NAMES_THE_AUTHOR author = \"Ada Lovelace\"\n"
      "`pragma protect `NAMES_THE_AUTHOR\n"
      "module m;\nendmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("module m;"));
}

// The spelling driving both halves in turn: a region naming its author is
// sealed by the encrypting half, and the envelope it produced is read back
// under the same key. The design comes out, the envelope's own expressions do
// not, and nothing about the naming costs the reading a diagnostic.
TEST(ProtectAuthorSyntax, AnEnvelopeCarryingTheExpressionIsReadBack) {
  ReadSource read(EncryptedRegionWriting(kAuthorDirective));
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

// The expression standing inside the envelope §34.5.3.1's and §34.5.4.1's words
// delimit, with those words written as source text rather than produced by the
// half above. That is the position the definition is really for: an envelope
// somebody else sealed, whose expressions stand in whatever order its producer
// wrote them, met by a tool that had no hand in writing it.
//
// What order another producer wrote its expressions in is not something a
// reader gets to settle, so the spelling is all the reader has to go on. The
// directive is consumed on it, the name reaches none of the design text, and
// the source standing on either side of the envelope arrives at the step after
// the preprocessor as it was written.
TEST(ProtectAuthorSyntax, TheExpressionInsideASealedModelIsRead) {
  std::string envelope = "`pragma protect begin_protected\n";
  envelope.append(kAuthorDirective);
  envelope.append("`pragma protect end_protected\n");
  ReadSource read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

// The expression on an envelope whose block is written in a scheme the region
// named, built from §34.5.9.1's own syntax: the keyword with a parenthesized
// list of subkeywords against it. The scheme is one the table sets aside rather
// than this implementation's own, so the block here is written in something the
// default says nothing about and a reading had to take the statement in to get
// the design back at all.
//
// The assertion on the produced text stands ahead of the reading on purpose. It
// is what says the scheme reached the envelope: without it a run that quietly
// fell back to this implementation's own writing would look exactly like a run
// that honored what the region stated, and the round trip would pass either
// way.
//
// What the naming has to survive here is a whole envelope written and read
// under a scheme of the source's choosing. The expression stands in the clear
// on it, once, in the spelling this subclause defines, and the design comes
// back out from under it.
TEST(ProtectAuthorSyntax, ARegionUnderAStatedEncodingCarriesTheExpression) {
  std::string stated = "`pragma protect encoding=(enctype=\"base64\")\n";
  stated.append(kAuthorDirective);
  std::string envelope = EncryptedRegionWriting(stated);
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_EQ(TimesWritten(envelope, kAuthorDirective), 1U);
  ReadSource read(envelope);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

}  // namespace
