// §34.5.8.1 Syntax, for the protect pragma keyword that carries whatever
// further the tool performing an encryption offered about itself.
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
// The name itself is the part of the spelling this subclause has that the one
// before it does not. Its opening characters spell the shorter tabulated name
// §34.5.7.1 defines, and the two are separate entries of §34.4's table rather
// than one name and a qualifier of it, so where one name ends and the other
// begins is something the spelling decides. A reading that matched the shorter
// name and went on from there would find a word this table does not list
// standing where a value belongs.
//
// What a reading may draw from the expression is nothing at all: §34.5.8 gives
// neither an encrypting tool nor a decrypting one anything to take out of it.
// So the whole of what the spelling binds at the reading end is the reading of
// the directive as a directive. A tool meets an envelope somebody else
// produced, whose expressions stand in whatever order that producer wrote them,
// and it has to consume the line without objecting to it and without letting
// any of it reach the design text. Which runs of characters are such a line and
// which are not is therefore what there is to observe here, and the spellings
// §22.5.1 admits that this keyword is not defined with -- a bare name, or a
// number or a parenthesized list written against it -- are consumed like any
// other pragma expression rather than distinguished, no reading having a value
// to draw from them to distinguish them by.
//
// All of it is preprocessor-stage. src/preprocessor/protect_keywords.cpp
// tabulates the name, which is what makes a value written against it a value
// the protect pragma puts in effect rather than one nothing records; the
// reading of the spelling as tokens is the pragma grammar in
// src/preprocessor/preprocessor_lines.cpp, whose expressions reach
// src/preprocessor/preprocessor_protect_keys.cpp; and
// src/preprocessor/protect_processing.cpp is the encrypting half, which draws
// nothing from the expression and so leaves a line carrying one among the text
// travelling into the block.
//
// Every input below is written as the real `pragma directive syntax of §22.11.
// §34.5.1.1's and §34.5.2.1's words delimit the region an encrypting tool
// transforms and §34.5.15's data_block is where the text that region sealed is
// carried; §34.5.3.1's and §34.5.4.1's words delimit a model an earlier
// encryption sealed already; §34.5.9.1's parenthesized value is the real syntax
// the list form is built from; and §34.5.30.1's keyword is the one written
// beside this one where an expression list is what carries them both.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key an IP author hands the encrypting half, and hands back to a tool
// reading what that half produced. Without one nothing is sealed and nothing is
// opened, so a reading that found no design text could not be told apart from a
// key that was never supplied.
constexpr std::string_view kExchangeKey = "globex-exchange-key";

// What a text offers further about the tool that sealed it. It holds spaces, so
// it can only have arrived anywhere as the value of an expression rather than
// as a stray word of a line.
constexpr std::string_view kFurtherWord = "assembled in Springfield";

// Where any directive writing this keyword with a value against it begins.
constexpr std::string_view kAnyOffering = "`pragma protect encrypt_agent_info=";

// The design a region seals. Nothing of it survives the alphabet an encrypted
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The two words delimiting a model an encryption sealed already, as a text
// holding one writes them.
constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

// Whether `text` writes `written` anywhere in it.
bool Carries(std::string_view text, std::string_view written) {
  return text.find(written) != std::string_view::npos;
}

// The expression this subclause defines, carrying `word` as the string written
// against the keyword.
std::string OffersFurther(std::string_view word) {
  std::string directive(kAnyOffering);
  directive.append("\"").append(word).append("\"\n");
  return directive;
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
// carries, which is the key and nothing besides. The readings that meet no
// envelope need none, and supplying one there would say nothing about the
// directive being read.
PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  return config;
}

// ---------------------------------------------------------------------------
// The spelling as a reading meets it.
// ---------------------------------------------------------------------------

// The directive as a tool reading source text meets it, which is as tokens of
// the pragma grammar rather than as characters of a line. The expression is one
// that grammar accepts, the directive is consumed like any other, and what the
// text offered reaches none of the design standing around it.
TEST(ProtectEncryptAgentInfoSyntax, TheKeywordWithAStringContributesNoText) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(OffersFurther(kFurtherWord)).append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

// The '=' with whitespace on either side of it, which is how the syntax line
// writes the expression. Whitespace separates the parts of a directive rather
// than belonging to any of them, so this is the same expression.
TEST(ProtectEncryptAgentInfoSyntax, PaddingAroundTheEqualsLeavesTheExpression) {
  PreprocFixture f;
  std::string src = "`pragma  protect  encrypt_agent_info  =  ";
  src.append("\"assembled in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

// The expression written on a directive holding a list, ahead of another one.
// Each expression of a list is spelled on its own, so a comma after the string
// ends this expression and the one after it is read in its own right.
TEST(ProtectEncryptAgentInfoSyntax, TheExpressionFirstInAListIsRead) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in Springfield\", comment=\"rev 3\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

// The same list in the other order. The reading reaches this expression having
// stepped over a string already, which is a different state to carry forward
// than the one the order above leaves it in.
TEST(ProtectEncryptAgentInfoSyntax, TheExpressionLastInAListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect comment=\"rev 3\", ";
  src.append("encrypt_agent_info=\"assembled in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
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
TEST(ProtectEncryptAgentInfoSyntax, TheExpressionInTheMiddleOfAListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect comment=\"rev 3\", ";
  src.append("encrypt_agent_info=\"assembled in Springfield\", ");
  src.append("comment=\"rev 4\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

// A block comment written between the keyword and the '=' that binds its value
// to it. A comment is not part of an expression list, and a closed one ends
// nothing, so what the grammar reads on either side of it is the one expression
// this subclause defines.
//
// The punctuation opening a comment is no token of this grammar, so a reading
// that had not stepped over it would meet a character it could make nothing of
// and report the directive rather than consume it.
TEST(ProtectEncryptAgentInfoSyntax, ABlockCommentInsideTheExpressionIsStepped) {
  PreprocFixture f;
  std::string src = "`pragma protect encrypt_agent_info ";
  src.append("/* what the sealer offered */ = ");
  src.append("\"assembled in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

// A comment is not a pragma expression, so a directive whose expression is
// followed by one wrote the expression and nothing else. Without this the
// string would have to be the last thing on its line to be the string.
TEST(ProtectEncryptAgentInfoSyntax, ACommentAfterTheStringLeavesTheExpression) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in Springfield\" // where it was sealed\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
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
TEST(ProtectEncryptAgentInfoSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  PreprocFixture f;
  std::string src = "`define OFFERS_MORE encrypt_agent_info = ";
  src.append("\"assembled in Springfield\"\n");
  src.append("`pragma protect `OFFERS_MORE\nmodule m;\nendmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// The expression standing inside the envelope §34.5.3.1's and §34.5.4.1's words
// delimit, with those words written as source text rather than produced by the
// encrypting half. That is the position the definition is really for: an
// envelope somebody else sealed, whose expressions stand in whatever order its
// producer wrote them, met by a tool that had no hand in writing it.
//
// What order another producer wrote its expressions in is not something a
// reader gets to settle, so the spelling is all the reader has to go on. The
// directive is consumed on it, the offered word reaches no design text, and the
// source on either side of the envelope arrives at the step after the
// preprocessor as it was written.
TEST(ProtectEncryptAgentInfoSyntax, TheExpressionInsideASealedModelIsRead) {
  PreprocFixture f;
  std::string sealed(kBeginProtected);
  sealed.append(OffersFurther(kFurtherWord)).append(kEndProtected);
  std::string read = Preprocess("module m;\n" + sealed + "endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

// ---------------------------------------------------------------------------
// Where the name begins and ends.
// ---------------------------------------------------------------------------

// The name broken at the underscore that joins the shorter tabulated name to
// what follows it. This is the sharpest negative of the name: every character
// the syntax line calls for is on the line and in its order, and one space
// stands inside the name.
//
// A pragma_keyword is one identifier, and a directive writing two of them side
// by side with no '=' between wrote neither of the spellings §22.5.1 gives a
// pragma expression, so the author is told rather than left with a name that
// was silently taken for the shorter one and a word the table does not list.
TEST(ProtectEncryptAgentInfoSyntax, TheNameBrokenAtItsUnderscoreIsRejected) {
  PreprocFixture f;
  std::string src = "`pragma protect encrypt_agent _info=";
  src.append("\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// What a string admits.
// ---------------------------------------------------------------------------

// A string is one written thing however much punctuation stands inside it, so a
// comma between the quotation marks separates nothing. A reading that took it
// for the comma between two expressions would end the value where the offered
// word is still running and be left with a string that never closes.
TEST(ProtectEncryptAgentInfoSyntax, AStringHoldingACommaIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled, in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

// The same for the punctuation that opens a one-line comment. A reading that
// looked for it before it looked for the closing quotation mark would end the
// directive inside the value and leave the rest of the string unaccounted for.
TEST(ProtectEncryptAgentInfoSyntax, AStringHoldingCommentMarksIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled // in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

// A quotation mark written behind a backslash is content of the string rather
// than the end of it, so a word written with one inside is still one string. A
// reading that ended the value at the first such mark would carry the rest of
// the line into the grammar as tokens the directive never wrote.
TEST(ProtectEncryptAgentInfoSyntax, AStringHoldingAnEscapedQuoteIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in \\\"Springfield\\\"\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

// The other spelling a string literal has: the triple-quoted form, which closes
// on a run of three marks rather than on one. It is a string, so it is a value
// this keyword is defined with.
//
// The value carries the character that form exists for. A lone quotation mark
// inside one closes nothing, so a word a producer could not have written in the
// ordinary spelling without escaping is still one string here -- and a reading
// that closed the form on a single mark would end the value inside the word and
// take the rest of it for tokens the directive never wrote. Written without
// that character the value would be read the same way whichever mark the form
// was thought to close on, and the spelling would go unobserved.
TEST(ProtectEncryptAgentInfoSyntax, ATripleQuotedStringWithAQuoteIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"\"\"assembled in \"Springfield\"\"\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

// A string with nothing between its quotation marks is a string, so the
// expression is the expression and the directive carrying it is consumed like
// any other. What it offers is nothing further, which is what that producer
// stated.
TEST(ProtectEncryptAgentInfoSyntax, AnEmptyStringIsAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(OffersFurther("")).append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// A string that writes this very expression inside itself. The letters between
// the quotation marks are characters of one keyword's value; the expression the
// directive wrote is the one whose keyword stands outside them.
TEST(ProtectEncryptAgentInfoSyntax, AStringSpellingTheExpressionIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"encrypt_agent_info=globex\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "encrypt_agent_info"));
}

// ---------------------------------------------------------------------------
// The spellings this keyword is not defined with.
// ---------------------------------------------------------------------------
//
// §22.5.1 gives a pragma expression one other spelling and a pragma_value three
// other spellings, and this keyword is defined with none of the four. They are
// separated from the section below because the reading does not turn them away:
// each is a pragma expression the grammar admits, and §34.5.8 gives no tool
// anything to draw from this keyword, so there is no value being taken for the
// wrong sort of thing and nothing for the reading to report. What every one of
// them leaves is a directive consumed and a design text none of its characters
// reached -- which is what the section above establishes of the defined
// spelling, reached over four other branches of the value grammar.

// The other spelling §22.5.1 gives a pragma expression: the keyword standing
// alone. This subclause defines the keyword with a value against it, so a
// directive writing it this way offers nothing further about any tool -- there
// is no string on the line to be what the syntax line calls for.
TEST(ProtectEncryptAgentInfoSyntax, TheKeywordStandingAloneWritesNoString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append("`pragma protect encrypt_agent_info\n").append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

// A number written where the string belongs. It is one written thing, which a
// string is too, so what separates it from the defined spelling is the sort of
// thing it is rather than how many tokens it took to write.
//
// The value reaches the design text no more than a string does, and the reading
// comes away with nothing to report: a number is a pragma_value, so a directive
// carrying one is a directive rather than an error, and the design on either
// side of it arrives at the step after the preprocessor as it was written.
TEST(ProtectEncryptAgentInfoSyntax, ANumberAgainstTheKeywordIsNotAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(kAnyOffering).append("7\n").append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// An identifier written where the string belongs. This is the closest of the
// four to the defined spelling: the letters a producer would have put between
// quotation marks, with the marks left off, so the same word arrives spelled as
// something other than a string.
//
// A word written bare cannot hold the spaces a string admits, which is what
// makes the quotation marks worth requiring rather than a formality, and the
// value here is written as one identifier's worth of letters for that reason.
TEST(ProtectEncryptAgentInfoSyntax, AnIdentifierAgainstTheKeywordIsNotAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(kAnyOffering).append("globex_sealer_7\n");
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "globex_sealer_7"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// The parenthesized spelling of a pragma_value, written with a list inside it,
// which is the real syntax §34.5.9.1 defines a keyword of this same table with.
// A list of further expressions names the parts of a value rather than being
// one, so it is not the one written thing this keyword is defined with, and a
// producer generating one would be naming subkeywords of its own devising where
// a word about a tool belongs.
//
// An empty pair of parentheses is not a fifth spelling but a failed writing of
// this one: the parenthesized form holds a list rather than an optional one, so
// the two differ in whether a value was written at all rather than in what sort
// of value it was. That is why it stands in the section below, among the
// spellings the reading turns away.
TEST(ProtectEncryptAgentInfoSyntax, AParenthesizedListIsNotOneWrittenThing) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(kAnyOffering);
  src.append("(name=\"Globex\", version=\"7\")\n");
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Globex"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

// ---------------------------------------------------------------------------
// The near misses the reading turns away.
// ---------------------------------------------------------------------------

// The '=' written with nothing after it. The spelling this keyword is defined
// with has a value on the right of the '=', so a directive that wrote the one
// without the other wrote neither of the two spellings §22.5.1 gives a pragma
// expression, and the author is told rather than left with a directive that
// quietly said nothing.
TEST(ProtectEncryptAgentInfoSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect encrypt_agent_info =\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The parenthesized spelling of a pragma_value written empty. That spelling
// holds a list of further expressions rather than an optional one, so an empty
// pair of parentheses is no value at all -- not the string this keyword is
// defined with, and not the other spelling either.
TEST(ProtectEncryptAgentInfoSyntax, AnEmptyParenthesizedValueIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect encrypt_agent_info=()\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A value that opens as a string and never closes. This is the closest input to
// the defined spelling the reading has to turn away: everything up to the last
// character is what the syntax line writes, and the one thing missing is the
// mark that makes the run of characters a string.
TEST(ProtectEncryptAgentInfoSyntax, AnUnclosedStringIsNoString) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in Springfield\n");
  Preprocess(src, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The same of the triple-quoted spelling, which closes on a run of three marks
// rather than on one. A value opened that way and closed with a single mark has
// not been closed, so the reading turns it away for the reason the ordinary
// spelling is turned away -- reached over the branch that looks for the longer
// terminator instead of the branch that looks for the shorter one.
TEST(ProtectEncryptAgentInfoSyntax, AnUnclosedTripleQuotedStringIsNoString) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"\"\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The keyword and a string with no '=' between them. The syntax line binds the
// two with that character, and §22.5.1 gives no spelling in which a keyword and
// a value stand side by side without it, so the directive wrote no expression
// this keyword is defined with and no expression the grammar admits either.
//
// This is the sharpest negative of the spelling itself: every character the
// syntax line calls for is on the line, and the one that binds them is not.
TEST(ProtectEncryptAgentInfoSyntax, AKeywordAndStringWithNoEqualsIsRejected) {
  PreprocFixture f;
  std::string src = "`pragma protect encrypt_agent_info ";
  src.append("\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The same letters written as an escaped identifier. A pragma_keyword is the
// simple form of an identifier, so the escaped spelling names no keyword at
// all: it stands where the grammar admits a value instead, which leaves the '='
// after it with nothing on its left that could carry a value.
//
// A reading that stepped over the backslash alone would find this keyword here
// and take an escaped identifier for the simple one the grammar calls for.
TEST(ProtectEncryptAgentInfoSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  PreprocFixture f;
  std::string src = "`pragma protect \\encrypt_agent_info = ";
  src.append("\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// The spelling carried through a whole envelope.
// ---------------------------------------------------------------------------

// The expression written inside a region an encrypting tool transforms, driven
// through both halves in turn: the region is sealed, and the envelope taking
// its place is handed straight back to a reading half holding the author's key.
//
// §34.5.8 has an encrypting tool draw nothing from the expression, so the line
// carrying one is text of the region like any other and travels into the block
// along with the design. That the region really was sealed is asserted before
// anything else -- neither the design nor the offered word stands in the clear
// on the envelope -- because a run that had transformed nothing would produce a
// text the reading half copies through, and the directive would then have been
// read straight out of the source rather than out of a block.
//
// What the spelling has to survive here is the whole round trip. The design
// comes back out from under the block, so the characters the block recovered to
// were read as source text; and the expression among them was the expression,
// so the directive was consumed on it and the offered word reaches none of the
// text the step after the preprocessor analyses.
TEST(ProtectEncryptAgentInfoSyntax, TheExpressionSealedIntoABlockIsReadBack) {
  std::string region = RegionHolding(OffersFurther(kFurtherWord));
  std::string envelope = EncryptEnvelopes(region, kExchangeKey);
  ASSERT_FALSE(Carries(envelope, kSealedDesign));
  ASSERT_FALSE(Carries(envelope, kFurtherWord));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

}  // namespace
