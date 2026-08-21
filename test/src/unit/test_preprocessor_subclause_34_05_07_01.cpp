// §34.5.7.1 Syntax, for the protect pragma keyword that names the tool which
// performed an encryption.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression:
//
//   The keyword is written with an '=' and a string against it.
//
// §22.5.1 offers a pragma expression two spellings -- a pragma_keyword standing
// alone, and a pragma_keyword with a pragma_value written against it -- and the
// words delimiting an envelope are defined with the first. This keyword is
// defined with the second, and the line goes further than choosing between the
// two: what stands on the right of the '=' is a string, which is one written
// thing. §22.5.1 spells a pragma_value two other ways as well -- a number or an
// identifier standing alone, and a parenthesized list of further expressions
// naming the parts of a value, which is the spelling §34.5.9.1 defines a
// keyword of this same table with -- so none of those is the value this keyword
// is defined with.
//
// Which half of the tool the spelling binds is what makes this subclause
// different from the ones defining keywords a tool reads something out of.
// §34.5.7 has an encrypting tool draw nothing from an expression its input
// wrote, and a decrypting tool draw nothing from one either, so no reading of
// this keyword turns on how the input spelled it. The half the spelling does
// bind is the writing one: the tool that performs an encryption generates the
// expression itself, and the spelling it generates has to be the spelling the
// standard defines, or a reader that goes looking for the name of the tool that
// sealed an envelope finds something that is not a string where the string
// belongs.
//
// The other half the spelling binds is the reading of the directive as a
// directive. A tool meets an envelope somebody else produced, whose expressions
// stand in whatever order that producer wrote them, and it has to consume the
// line without objecting to it and without letting any of it reach the design
// text. That is the pragma grammar's reading rather than this keyword's, and
// what this subclause contributes to it is which spellings a conforming
// producer may have used.
//
// All of it is preprocessor-stage. src/preprocessor/protect_keywords.h holds
// the name and src/preprocessor/protect_keywords.cpp writes the expression, in
// the keyword-equals-string form, out of the description an envelope carries;
// src/preprocessor/protect_envelope_output.h holds the name this implementation
// identifies itself by and src/preprocessor/protect_envelope_output.cpp places
// the directive inside the envelope; and the reading of the same spelling as
// tokens is the pragma grammar in src/preprocessor/preprocessor_lines.cpp,
// whose expressions reach src/preprocessor/preprocessor_protect_keys.cpp.
//
// Every input below is written as the real `pragma directive syntax of §22.11.
// §34.5.1.1's and §34.5.2.1's words delimit the region an encrypting tool
// transforms; §34.5.3.1's and §34.5.4.1's words delimit a model an earlier
// encryption sealed already; §34.5.9.1's parenthesized value is the real syntax
// the list form is built from; and §34.5.30.1's keyword is the one written
// beside this one where an expression list is what carries them both.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key an IP author hands the encrypting half, and hands back to a tool
// reading what that half produced. Without one nothing is sealed and nothing is
// opened, so a reading that found no design text could not be told apart from a
// key that was never supplied.
constexpr std::string_view kExchangeKey = "globex-exchange-key";

// The name a source text writes against the keyword, standing for whatever tool
// the text passed through before this one reached it. It holds spaces, so it
// can only have arrived anywhere as the value of an expression rather than as a
// stray word of a line.
constexpr std::string_view kAgentName = "Globex Sealer 7";

// The directive carrying that name, in the spelling this subclause defines.
constexpr std::string_view kAgentDirective =
    "`pragma protect encrypt_agent=\"Globex Sealer 7\"\n";

// Where any directive writing this keyword with a value against it begins. The
// '=' keeps the reading off the longer tabulated name that carries anything
// further about an encrypting tool.
constexpr std::string_view kAnyAgentExpression =
    "`pragma protect encrypt_agent=";

// The design a region seals. Nothing of it survives the alphabet an encrypted
// block is written in, so finding it outside a block is finding a region that
// was never sealed.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The two words delimiting a model an encryption sealed already, as a text
// holding one writes them.
constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// How many times `needle` is written in `text`, counting the writings that do
// not overlap.
size_t TimesWritten(std::string_view text, std::string_view needle) {
  size_t count = 0;
  for (size_t at = text.find(needle); at != std::string_view::npos;
       at = text.find(needle, at + needle.size())) {
    ++count;
  }
  return count;
}

// The directive this implementation generates for an envelope of its own
// making: the keyword, an '=', and its own name written as a string.
std::string GeneratedExpression() {
  return std::string("`pragma protect encrypt_agent=\"")
      .append(kEncryptAgent)
      .append("\"\n");
}

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with `written` and
// then the design between them. The design comes last so that a line the
// encryption passed over is a line that went into the block ahead of it.
std::string RegionAround(std::string_view written) {
  std::string text = "`pragma protect begin\n";
  text.append(written).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The text standing where that region was written, for a tool holding the
// author's key.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kExchangeKey);
}

// A source text read through the preprocessor, with the diagnostics the reading
// raised kept beside the text it produced.
//
// `key` is what a user supplies for opening the protected regions an input
// carries. The readings that meet no envelope need none, and supplying one
// there would say nothing about the directive being read.
struct ReadBack {
  // What the reading is configured with, which is the key and nothing besides.
  // It stands ahead of the constructor because the constructor's own body is
  // what calls it.
  static PreprocConfig Configured(std::string_view key) {
    PreprocConfig config;
    config.protect_key = std::string(key);
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit ReadBack(const std::string& src, std::string_view key = {}) {
    Preprocessor pp(mgr, diag, Configured(key));
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// ---------------------------------------------------------------------------
// The spelling the tool generates.
// ---------------------------------------------------------------------------

// The syntax line read where it binds this implementation: the expression the
// encrypting half writes into an envelope of its own making is the keyword with
// a string against it. The region really was sealed -- its design is gone from
// the produced text -- so the expression describes an envelope rather than
// standing over a region nothing happened to.
TEST(ProtectEncryptAgentSyntax, TheToolWritesTheKeywordWithAStringAgainstIt) {
  std::string envelope = Encrypted(RegionAround(""));
  EXPECT_FALSE(Holds(envelope, kSealedDesign));
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
}

// The nearest spelling the generated directive is not written in. §22.5.1
// admits a bare identifier as a pragma_value, and the tool's own name is one
// identifier's worth of letters, so writing it without the quotation marks
// would still leave a directive the pragma grammar accepts -- and one that is
// not the expression this subclause defines.
TEST(ProtectEncryptAgentSyntax, TheGeneratedValueIsNotWrittenAsABareName) {
  std::string envelope = Encrypted(RegionAround(""));
  std::string unquoted(kAnyAgentExpression);
  unquoted.append(kEncryptAgent);
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
  EXPECT_FALSE(Holds(envelope, unquoted));
}

// The other spelling §22.5.1 gives a pragma expression, which this keyword is
// not defined with: the keyword standing alone writes no string, so an envelope
// carrying it would name no tool at all. Exactly one expression writing this
// keyword stands in the clear on the envelope, and it is the defined one.
TEST(ProtectEncryptAgentSyntax, TheToolNeverWritesTheKeywordStandingAlone) {
  std::string envelope = Encrypted(RegionAround(""));
  EXPECT_EQ(TimesWritten(envelope, kAnyAgentExpression), 1U);
  EXPECT_FALSE(Holds(envelope, "`pragma protect encrypt_agent\n"));
}

// The two halves reading one spelling: the envelope the encrypting half wrote
// is handed straight back to the reading half under the same key. The directive
// the writing half generated is one the pragma grammar accepts, so the reading
// costs no diagnostic, the design comes back, and the name of the tool that
// sealed it reaches none of the text the step after the preprocessor analyses.
TEST(ProtectEncryptAgentSyntax, TheGeneratedExpressionIsReadBackAsWritten) {
  ReadBack read(Encrypted(RegionAround("")), kExchangeKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kEncryptAgent));
}

// The closest input to the defined spelling that an envelope's description may
// not be built from: a parenthesized list of further expressions written where
// the string belongs. A list is not one written thing, so it is not this
// keyword's value, and a producer that generated one would be naming
// subkeywords of its own devising rather than a tool.
//
// A region writing it is sealed like any other text, and the envelope taking
// that region's place still carries the one expression the writing half
// generated, in the defined spelling.
TEST(ProtectEncryptAgentSyntax, AParenthesizedListIsNotTheGeneratedValue) {
  std::string listed =
      "`pragma protect encrypt_agent=(name=\"Globex\", version=\"7\")\n";
  std::string envelope = Encrypted(RegionAround(listed));
  EXPECT_TRUE(Holds(envelope, kBeginProtected));
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
  EXPECT_EQ(TimesWritten(envelope, kAnyAgentExpression), 1U);
}

// ---------------------------------------------------------------------------
// The same spelling met by the reading half.
// ---------------------------------------------------------------------------

// The directive as a tool reading source text meets it, which is as tokens of
// the pragma grammar rather than as characters of a line. The expression is one
// that grammar accepts, the directive is consumed like any other, and the name
// reaches none of the design text standing around it.
TEST(ProtectEncryptAgentSyntax, TheKeywordWithAStringContributesNoText) {
  ReadBack read("module m;\n" + std::string(kAgentDirective) + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

// The '=' with whitespace on either side of it, which is how the syntax line
// writes the expression. Whitespace separates the parts of a directive rather
// than belonging to any of them, so this is the same expression.
TEST(ProtectEncryptAgentSyntax, PaddingAroundTheEqualsLeavesTheExpression) {
  ReadBack read("`pragma  protect  encrypt_agent  =  \"Globex Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

// The expression written on a directive holding a list, ahead of another one.
// Each expression of a list is spelled on its own, so a comma after the string
// ends this expression and the one after it is read in its own right.
TEST(ProtectEncryptAgentSyntax, TheExpressionFirstInAListIsRead) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"Globex Sealer 7\", comment=\"rev 3\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

// The same list in the other order. The reading reaches this expression having
// stepped over a string already, which is a different state to carry forward
// than the one the order above leaves it in.
TEST(ProtectEncryptAgentSyntax, TheExpressionLastInAListIsRead) {
  ReadBack read(
      "`pragma protect comment=\"rev 3\", encrypt_agent=\"Globex Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

// The third position a list puts an expression in, with one expression on
// either side of it. The reading has to arrive here off a comma and leave on
// one, which neither of the two orders above asks of it: an expression at
// either end of a list is bounded by the directive on one side.
//
// The neighbours are two writings of the keyword §34.5.30.1 defines. Writing it
// twice is what §34.4's lexical scope settles rather than something this
// spelling turns on, so the neighbours say nothing about the expression between
// them beyond standing there.
//
// §34.5.30.2 leaves them where they are. It has a comment output in cleartext
// ahead of the data block of the begin-end it was found in, and these stand
// inside no begin-end at all.
TEST(ProtectEncryptAgentSyntax, TheExpressionInTheMiddleOfAListIsRead) {
  std::string listed = "`pragma protect comment=\"rev 3\", ";
  listed.append("encrypt_agent=\"Globex Sealer 7\", comment=\"rev 4\"\n");
  ReadBack read(listed);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

// A block comment written between the keyword and the '=' that binds its value
// to it. A comment is not part of an expression list, and a closed one ends
// nothing, so what the grammar reads on either side of it is the one expression
// this subclause defines.
//
// The punctuation opening a comment is no token of this grammar, so a reading
// that had not stepped over it would meet a character it could make nothing of
// and report the directive rather than consume it.
TEST(ProtectEncryptAgentSyntax, ABlockCommentInsideTheExpressionIsStepped) {
  ReadBack read(
      "`pragma protect encrypt_agent /* the sealer */ = \"Globex Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

// A comment is not a pragma expression, so a directive whose expression is
// followed by one wrote the expression and nothing else. Without this the
// string would have to be the last thing on its line to be the string.
TEST(ProtectEncryptAgentSyntax, ACommentAfterTheStringLeavesTheExpression) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"Globex Sealer 7\" // who sealed it\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

// The expression need not be written in the source as the expression: a
// directive's text is ordinary source text, so a macro usage in it is
// substituted before the pragma grammar reads it. The whole of the expression
// arrives that way here, punctuation and all, so what the grammar reads as the
// keyword, the '=' and the string is text no line of the source wrote in that
// order.
//
// A directive the substitution had not reached would still carry the macro's
// own punctuation, which is no token of this grammar, so the reading coming
// away with nothing to report is the substitution having happened first.
TEST(ProtectEncryptAgentSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  ReadBack read(
      "`define NAMES_THE_AGENT encrypt_agent = \"Globex Sealer 7\"\n"
      "`pragma protect `NAMES_THE_AGENT\n"
      "module m;\nendmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
  EXPECT_TRUE(read.Holds("module m;"));
}

// The expression standing inside the envelope §34.5.3.1's and §34.5.4.1's words
// delimit, with those words written as source text rather than produced by the
// encrypting half. That is the position the definition is really for: an
// envelope somebody else sealed, whose expressions stand in whatever order its
// producer wrote them, met by a tool that had no hand in writing it.
//
// What order another producer wrote its expressions in is not something a
// reader gets to settle, so the spelling is all the reader has to go on. The
// directive is consumed on it, the name reaches no design text, and the source
// on either side of the envelope arrives at the step after the preprocessor as
// it was written.
TEST(ProtectEncryptAgentSyntax, TheExpressionInsideASealedModelIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append(kAgentDirective).append(kEndProtected);
  ReadBack read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

// ---------------------------------------------------------------------------
// What a string admits.
// ---------------------------------------------------------------------------

// A string is one written thing however much punctuation stands inside it, so a
// comma between the quotation marks separates nothing. A reading that took it
// for the comma between two expressions would end the value where the name is
// still running and be left with a string that never closes.
TEST(ProtectEncryptAgentSyntax, AStringHoldingACommaIsOneValue) {
  ReadBack read("`pragma protect encrypt_agent=\"Globex, Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

// The same for the punctuation that opens a one-line comment. A reading that
// looked for it before it looked for the closing quotation mark would end the
// directive inside the value and leave the rest of the string unaccounted for.
TEST(ProtectEncryptAgentSyntax, AStringHoldingCommentPunctuationIsOneValue) {
  ReadBack read("`pragma protect encrypt_agent=\"Globex // Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

// A quotation mark written behind a backslash is content of the string rather
// than the end of it, so a name written with one inside is still one string. A
// reading that ended the value at the first such mark would carry the rest of
// the line into the grammar as tokens the directive never wrote.
TEST(ProtectEncryptAgentSyntax, AStringHoldingAnEscapedQuoteIsOneValue) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"Globex \\\"the Sealer\\\" 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

// The other spelling a string literal has: the triple-quoted form, which closes
// on a run of three marks rather than on one. It is a string, so it is a value
// this keyword is defined with.
//
// The value carries the character that form exists for. A lone quotation mark
// inside one closes nothing, so a name a producer could not have written in the
// ordinary spelling without escaping is still one string here -- and a reading
// that closed the form on a single mark would end the value inside the name and
// take the rest of it for tokens the directive never wrote. Written without
// that character the value would be read the same way whichever mark the form
// was thought to close on, and the spelling would go unobserved.
TEST(ProtectEncryptAgentSyntax, ATripleQuotedStringHoldingAQuoteIsOneValue) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"\"\"Globex \"Sealer\" 7\"\"\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

// A string with nothing between its quotation marks is a string, so the
// expression is the expression and the directive carrying it is consumed like
// any other. What it names is an encryption whose tool is written as nobody,
// which is what that producer stated.
TEST(ProtectEncryptAgentSyntax, AnEmptyStringIsAString) {
  ReadBack read("module m;\n`pragma protect encrypt_agent=\"\"\nendmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("pragma"));
  EXPECT_TRUE(read.Holds("module m;"));
}

// A string that writes this very expression inside itself. The letters between
// the quotation marks are characters of one keyword's value; the expression the
// directive wrote is the one whose keyword stands outside them.
TEST(ProtectEncryptAgentSyntax, AStringSpellingTheExpressionIsOneValue) {
  ReadBack read("`pragma protect encrypt_agent=\"encrypt_agent=globex\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("encrypt_agent"));
}

// ---------------------------------------------------------------------------
// The near misses the reading turns away.
// ---------------------------------------------------------------------------

// The '=' written with nothing after it. The spelling this keyword is defined
// with has a value on the right of the '=', so a directive that wrote the one
// without the other wrote neither of the two spellings §22.5.1 gives a pragma
// expression, and the author is told rather than left with a directive that
// quietly said nothing.
TEST(ProtectEncryptAgentSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  ReadBack read("`pragma protect encrypt_agent =\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The parenthesized spelling of a pragma_value written empty. That spelling
// holds a list of further expressions rather than an optional one, so an empty
// pair of parentheses is no value at all -- not the string this keyword is
// defined with, and not the other spelling either.
TEST(ProtectEncryptAgentSyntax, AnEmptyParenthesizedValueIsNoExpression) {
  ReadBack read("`pragma protect encrypt_agent=()\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// A value that opens as a string and never closes. This is the closest input to
// the defined spelling the reading has to turn away: everything up to the last
// character is what the syntax line writes, and the one thing missing is the
// mark that makes the run of characters a string.
TEST(ProtectEncryptAgentSyntax, AnUnclosedStringIsNoString) {
  ReadBack read("`pragma protect encrypt_agent=\"Globex Sealer 7\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

// The same of the triple-quoted spelling, which closes on a run of three marks
// rather than on one. A value opened that way and closed with a single mark
// has not been closed, so the reading turns it away for the reason the ordinary
// spelling is turned away -- reached over the branch that looks for the longer
// terminator instead of the branch that looks for the shorter one.
TEST(ProtectEncryptAgentSyntax, AnUnclosedTripleQuotedStringIsNoString) {
  ReadBack read("`pragma protect encrypt_agent=\"\"\"Globex Sealer 7\"\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

// The keyword and a string with no '=' between them. The syntax line binds the
// two with that character, and §22.5.1 gives no spelling in which a keyword and
// a value stand side by side without it, so the directive wrote no expression
// this keyword is defined with and no expression the grammar admits either.
//
// This is the sharpest negative of the spelling itself: every character the
// syntax line calls for is on the line, and the one that binds them is not.
TEST(ProtectEncryptAgentSyntax, TheKeywordAndAStringWithNoEqualsIsRejected) {
  ReadBack read("`pragma protect encrypt_agent \"Globex Sealer 7\"\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The same letters written as an escaped identifier. A pragma_keyword is the
// simple form of an identifier, so the escaped spelling names no keyword at
// all: it stands where the grammar admits a value instead, which leaves the '='
// after it with nothing on its left that could carry a value.
//
// A reading that stepped over the backslash alone would find this keyword here
// and take an escaped identifier for the simple one the grammar calls for.
TEST(ProtectEncryptAgentSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  ReadBack read("`pragma protect \\encrypt_agent = \"Globex Sealer 7\"\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// ---------------------------------------------------------------------------
// The spelling carried through a whole envelope.
// ---------------------------------------------------------------------------

// The expression on an envelope whose blocks are written in a scheme the region
// stated, built from §34.5.9.1's own syntax: that keyword with a parenthesized
// list of subkeywords against it. The scheme is one the standard sets aside
// rather than this implementation's own, so the block here is written in
// something the default says nothing about and a reading had to take the
// statement in to get the design back at all.
//
// Whether the stated scheme reached the envelope is asserted before anything
// else, and the reading is only allowed to proceed once it has. A run that fell
// back to this implementation's own writing would produce an envelope that
// opens just as readily, so a round trip on its own would come out the same
// whether the statement was honored or ignored.
//
// What the spelling has to survive here is a whole envelope written and read
// under a scheme the source chose. The generated expression stands in the clear
// on it, once, as the keyword with a string against it -- outside the block, so
// none of the scheme applies to it -- and the design comes back out from under
// it.
TEST(ProtectEncryptAgentSyntax, ARegionUnderAStatedEncodingCarriesIt) {
  std::string stated = "`pragma protect encoding=(enctype=\"base64\")\n";
  std::string envelope = Encrypted(RegionAround(stated));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
  EXPECT_EQ(TimesWritten(envelope, kAnyAgentExpression), 1U);
  ReadBack read(envelope, kExchangeKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

}  // namespace
