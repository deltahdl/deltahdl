// §22.11 `pragma -- Syntax 22-8 and the surrounding prose.
//
// The directive is a preprocessor-stage rule: src/preprocessor/preprocessor.cpp
// recognizes the keyword, checks the directive text against Syntax 22-8, and
// consumes it. Everything exercised here is observed through that path.

#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// Preprocesses `src` while keeping the Preprocessor alive so the directive
// state it accumulated can be read back afterwards. Used by the tests that
// show a pragma leaves the interpretation of the source text alone.
struct PragmaStateRun {
  std::string output;
  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;
  bool in_celldefine = false;
  bool has_timescale = false;
  std::vector<std::string> cell_modules;
};

PragmaStateRun RunForState(const std::string& src, PreprocFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  PragmaStateRun run;
  run.output = pp.Preprocess(fid);
  run.default_nettype = pp.DefaultNetType();
  run.unconnected_drive = pp.UnconnectedDrive();
  run.in_celldefine = pp.InCelldefine();
  run.has_timescale = pp.HasTimescale();
  run.cell_modules = pp.CellModuleNames();
  return run;
}

std::string TrimAll(std::string s) {
  auto begin = s.find_first_not_of(" \t\n\r");
  if (begin == std::string::npos) return "";
  s.erase(0, begin);
  s.erase(s.find_last_not_of(" \t\n\r") + 1);
  return s;
}

// ---------------------------------------------------------------------------
// pragma ::= `pragma pragma_name [ pragma_expression { , pragma_expression } ]
// ---------------------------------------------------------------------------

// The expression list is bracketed in the production, so a pragma_name on its
// own is a complete directive.
TEST(PragmaDirective, NameAlone_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaDirective, NameWithCommaSeparatedList_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1, expr2, expr3\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The pragma_name is not optional, so the keyword alone names no pragma.
TEST(PragmaDirective, KeywordAlone_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaDirective, OnlyWhitespaceAfterKeyword_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma   \n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A comma joins two pragma_expressions; it may not stand where one is missing.
TEST(PragmaDirective, TrailingComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1,\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaDirective, LeadingComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma , expr1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaDirective, EmptyListElement_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1, , expr2\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The production separates list elements with commas, so two pragma_expressions
// written side by side are not a list.
TEST(PragmaDirective, AdjacentExpressionsWithoutComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1 expr2\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The keyword and the pragma_name are separate lexical elements, so a name
// character flush against the keyword makes the line a macro usage instead.
TEST(PragmaDirective, KeywordFlushAgainstName_IsMacroUsage) {
  PreprocFixture f;
  auto out = Preprocess("`define pragma_like wire w;\n`pragma_like\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire w;"), std::string::npos);
}

// '$' is an identifier character too, so it binds the name to the keyword the
// same way a letter does.
TEST(PragmaDirective, KeywordFlushAgainstDollarName_IsMacroUsage) {
  PreprocFixture f;
  auto out = Preprocess("`define pragma$x wire w;\n`pragma$x\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire w;"), std::string::npos);
}

// The directive extends over its whole expression list, none of which reaches
// the token stream handed to the lexer.
TEST(PragmaDirective, ProducesNoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma my_pragma key = val, 42\n", f);
  EXPECT_TRUE(TrimAll(out).empty());
}

// Nothing requires the backtick to sit in the first column.
TEST(PragmaDirective, IndentedDirective_Accepted) {
  PreprocFixture f;
  auto out =
      Preprocess("module m;\n    `pragma my_pragma key = 1\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("endmodule"), std::string::npos);
}

// A comment is not part of the expression list, so it neither extends the
// directive nor contributes a token the grammar has to account for.
TEST(PragmaDirective, TrailingLineComment_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma key = 1 // a note about the pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaDirective, EmbeddedBlockComment_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma /* a note */ key = 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A block comment opened on the directive line ends the pragma text, and the
// comment itself keeps running afterwards. A directive written inside it is
// therefore still commented out, which is what distinguishes the comment being
// carried forward from it being dropped along with the directive line.
TEST(PragmaDirective, OpenBlockCommentKeepsRunningPastTheDirective) {
  PreprocFixture f;
  auto out = Preprocess(
      "`pragma my_pragma key = 1 /* opened here\n"
      "`define SHOULD_STAY_UNDEFINED\n"
      "*/\n"
      "`ifdef SHOULD_STAY_UNDEFINED\n"
      "wire bad;\n"
      "`else\n"
      "wire good;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out.find("wire bad;"), std::string::npos);
  EXPECT_NE(out.find("wire good;"), std::string::npos);
}

// pragma_value recurses through pragma_expression, so the nesting has no fixed
// depth.
TEST(PragmaDirective, DeeplyNestedExpressionList_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma outer = (mid = (inner1, inner2), tail), last\n",
             f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaDirective, NoTrailingNewline_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaDirective, TrailingWhitespaceAfterName_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma   \n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// pragma_name ::= simple_identifier
// ---------------------------------------------------------------------------

TEST(PragmaName, UnderscoreLed_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma _my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A simple_identifier admits digits, underscores, and '$' after its first
// character.
TEST(PragmaName, DigitsUnderscoreDollarTail_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma p1_a$b2\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaName, DigitLed_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma 123\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaName, String_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma \"my_pragma\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// '$' opens a system name, which is not a simple_identifier.
TEST(PragmaName, DollarLed_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma $my_pragma\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The closest legal-identifier negative: an escaped identifier is an
// identifier, but the production restricts a pragma_name to the simple form.
TEST(PragmaName, EscapedIdentifier_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma \\my_pragma \n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A pragma_name is only required to be a simple_identifier; nothing bars one
// that happens to spell a compiler directive keyword, and the word must not be
// acted on as a directive of its own.
TEST(PragmaName, SpelledLikeADirectiveKeyword_Accepted) {
  PreprocFixture f;
  auto out = Preprocess("`pragma define\nwire w;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(TrimAll(out), "wire w;");
}

TEST(PragmaName, ParenthesizedList_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma (a, b)\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// pragma_expression ::= pragma_keyword
//                     | pragma_keyword = pragma_value
//                     | pragma_value
// ---------------------------------------------------------------------------

TEST(PragmaExpression, BareKeyword_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma some_keyword\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaExpression, BareNumberValue_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma 42\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaExpression, BareStringValue_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma \"hello world\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaExpression, BareParenthesizedValue_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, b, c)\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaExpression, MixedFormsInOneList_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma bare, key = 1, \"text\", (x, y = 2)\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Every alternative starts with a pragma_keyword or a pragma_value; none of
// them starts with '='.
TEST(PragmaExpression, EqualsWithoutKeyword_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma = val1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaExpression, KeywordWithoutValue_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma key1 =\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The right side of '=' is a pragma_value, and '=' is not one.
TEST(PragmaExpression, DoubledEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma key1 = = val1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A pragma_value is not itself a pragma_expression, so assignments do not
// chain.
TEST(PragmaExpression, ChainedEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma a = b = c\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// pragma_keyword ::= simple_identifier
// ---------------------------------------------------------------------------

TEST(PragmaKeyword, DigitsUnderscoreDollarTail_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma k1_a$b2 = 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaKeyword, UnderscoreLed_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma _key = 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaKeyword, NumberOnLeftOfEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma 42 = val1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaKeyword, StringOnLeftOfEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma \"key\" = val1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// An escaped identifier is a legal pragma_value but not a legal
// pragma_keyword, so it cannot take a value of its own.
TEST(PragmaKeyword, EscapedIdentifierOnLeftOfEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma \\key$1 = val1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A parenthesized list is a pragma_value, and a pragma_value cannot take a
// value of its own.
TEST(PragmaKeyword, ParenthesizedListOnLeftOfEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, b) = val1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// pragma_value ::= ( pragma_expression { , pragma_expression } )
//                | number | string | identifier
// ---------------------------------------------------------------------------

TEST(PragmaValue, SizedBasedNumber_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma width = 8'hFF\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A based literal may leave its size off.
TEST(PragmaValue, UnsizedBasedNumber_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma mask = 'h1F\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, UnbasedUnsizedNumber_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma fill = '1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A binary literal may carry unknown and high-impedance digits.
TEST(PragmaValue, BinaryNumberWithFourStateDigits_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma mask = 4'b10x1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, UnderscoreSeparatedNumber_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma depth = 1_000\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, RealNumber_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma ratio = 3.25\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The exponent of a real number carries its own sign.
TEST(PragmaValue, RealNumberWithSignedExponent_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma ratio = 1.5e-3\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A leading sign is not part of a number, and nothing else in the production
// admits one either.
TEST(PragmaValue, LeadingSign_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma offset = -5\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaValue, EmptyString_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, StringWithEscapedQuote_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"a \\\" b\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Punctuation inside a string is part of the string, not structure the
// expression grammar has to account for.
TEST(PragmaValue, StringContainingListPunctuation_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"a, b = (c)\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A triple-quoted literal is one string, so the plain quotes inside it are
// content rather than terminators that would split it into several values.
TEST(PragmaValue, TripleQuotedString_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"\"\"a \"quoted\" phrase\"\"\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, UnterminatedTripleQuotedString_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"\"\"never closed\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaValue, SimpleIdentifier_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma mode = fast\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A pragma_value is an identifier, which unlike a pragma_name or a
// pragma_keyword also covers the escaped form.
TEST(PragmaValue, EscapedIdentifier_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma mode = \\fast$mode \n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, ParenthesizedKeywordValueList_Accepted) {
  PreprocFixture f;
  Preprocess(
      "`pragma my_pragma encoding = ( enctype = \"uuencode\" , "
      "line_length = 64 , bytes = 190 )\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, NestedParentheses_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, (b, c))\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The parenthesized form holds a list, not an optional one.
TEST(PragmaValue, EmptyParentheses_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma ()\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaValue, UnbalancedOpenParen_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, b\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The inner list must close before the outer one does.
TEST(PragmaValue, UnbalancedNestedParen_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, (b, c)\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaValue, StrayCloseParen_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma a)\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaValue, ParenthesizedListMissingComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a b)\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaValue, UnterminatedString_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"unterminated\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// An unrecognized pragma_name has no effect on the interpretation of the
// SystemVerilog source text.
// ---------------------------------------------------------------------------

TEST(PragmaUnrecognized, SurroundingSourceTextPreserved) {
  PreprocFixture f;
  auto out = Preprocess(
      "wire a;\n"
      "`pragma totally_unknown_xyz key = val\n"
      "wire b;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire a;"), std::string::npos);
  EXPECT_NE(out.find("wire b;"), std::string::npos);
  EXPECT_EQ(out.find("totally_unknown_xyz"), std::string::npos);
}

// The pragma sits between two directives whose state the elaborator reads; if
// it had an effect on interpretation, one of them would be disturbed.
TEST(PragmaUnrecognized, DefaultNettypeStatePreserved) {
  PreprocFixture f;
  auto run = RunForState(
      "`default_nettype none\n"
      "`pragma totally_unknown_xyz mode = fast\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(run.default_nettype, NetType::kNone);
}

TEST(PragmaUnrecognized, UnconnectedDriveStatePreserved) {
  PreprocFixture f;
  auto run = RunForState(
      "`unconnected_drive pull1\n"
      "`pragma totally_unknown_xyz mode = fast\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(run.unconnected_drive, NetType::kTri1);
}

// A pragma written inside a cell-module region neither closes the region nor
// hides the module that follows it from the cell tagging.
TEST(PragmaUnrecognized, CelldefineRegionPreserved) {
  PreprocFixture f;
  auto run = RunForState(
      "`celldefine\n"
      "`pragma totally_unknown_xyz\n"
      "module cell_m;\nendmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(run.in_celldefine);
  ASSERT_EQ(run.cell_modules.size(), 1u);
  EXPECT_EQ(run.cell_modules[0], "cell_m");
}

TEST(PragmaUnrecognized, TimescaleStatePreserved) {
  PreprocFixture f;
  auto run = RunForState(
      "`timescale 1ns/1ps\n"
      "`pragma totally_unknown_xyz\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(run.has_timescale);
}

// Nothing in the clause confines the directive to the outside of a design
// element, unlike `timescale or `default_nettype.
TEST(PragmaUnrecognized, InsideDesignElement_Accepted) {
  PreprocFixture f;
  auto out = Preprocess(
      "module m;\n"
      "`pragma totally_unknown_xyz\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire w;"), std::string::npos);
  EXPECT_NE(out.find("endmodule"), std::string::npos);
}

// Macro definitions are part of how the source text is interpreted, so a
// pragma standing between a definition and its use must leave it intact.
TEST(PragmaUnrecognized, MacroTableUnchangedAcrossAPragma) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define WIDTH 8\n"
      "`pragma totally_unknown_xyz mode = fast\n"
      "wire [`WIDTH-1:0] bus;\n"
      "`ifdef WIDTH\n"
      "wire still_defined;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire [8-1:0] bus;"), std::string::npos);
  EXPECT_NE(out.find("still_defined"), std::string::npos);
}

// The words inside a pragma are pragma_expressions, not directives: naming a
// macro there does not define one.
TEST(PragmaUnrecognized, PragmaTextDoesNotDefineAMacro) {
  PreprocFixture f;
  auto out = Preprocess(
      "`pragma totally_unknown_xyz define, NEVER_DEFINED = 1\n"
      "`ifdef NEVER_DEFINED\n"
      "wire bad;\n"
      "`else\n"
      "wire good;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out.find("wire bad;"), std::string::npos);
  EXPECT_NE(out.find("wire good;"), std::string::npos);
}

// Since no pragma_name is recognized, the name cannot select any behavior:
// two sources differing only in it must preprocess to the same text.
TEST(PragmaUnrecognized, DifferentUnknownNamesGiveIdenticalOutput) {
  PreprocFixture f1;
  auto out1 = Preprocess(
      "`pragma unknown_name_one key = 1\n"
      "module m;\n  wire w;\nendmodule\n",
      f1);
  PreprocFixture f2;
  auto out2 = Preprocess(
      "`pragma a_completely_different_name key = 1\n"
      "module m;\n  wire w;\nendmodule\n",
      f2);
  EXPECT_FALSE(f1.diag.HasErrors());
  EXPECT_FALSE(f2.diag.HasErrors());
  EXPECT_EQ(out1, out2);
}

TEST(PragmaUnrecognized, ConsecutivePragmasAllConsumed) {
  PreprocFixture f;
  auto out = Preprocess(
      "`pragma first_pragma\n"
      "`pragma second_pragma key = 1\n"
      "`pragma third_pragma (a, b)\n"
      "wire w;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(TrimAll(out), "wire w;");
}

// ---------------------------------------------------------------------------
// Conditional compilation gating: a directive inside a branch that is compiled
// away is not part of the source description, so its text is never checked.
// ---------------------------------------------------------------------------

TEST(PragmaConditional, MalformedPragmaInActiveBranchIsDiagnosed) {
  PreprocFixture f;
  Preprocess(
      "`define ON\n"
      "`ifdef ON\n"
      "`pragma 123\n"
      "`endif\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaConditional, MalformedPragmaInInactiveBranchIsIgnored) {
  PreprocFixture f;
  Preprocess(
      "`ifdef NEVER_DEFINED\n"
      "`pragma 123\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaConditional, WellFormedPragmaInActiveBranchIsAccepted) {
  PreprocFixture f;
  Preprocess(
      "`define ON\n"
      "`ifdef ON\n"
      "`pragma some_pragma key = 1\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// The directive text is ordinary source, so text macros supply pragma input.
// ---------------------------------------------------------------------------

TEST(PragmaMacroInput, MacroSuppliesPragmaName) {
  PreprocFixture f;
  Preprocess("`define PNAME my_pragma\n`pragma `PNAME\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaMacroInput, MacroSuppliesValue) {
  PreprocFixture f;
  Preprocess("`define MY_VAL 42\n`pragma my_pragma key = `MY_VAL\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaMacroInput, MacroSuppliesWholeExpressionList) {
  PreprocFixture f;
  Preprocess("`define MY_LIST a, b = 1, (c, d)\n`pragma my_pragma `MY_LIST\n",
             f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Substitution happens before the grammar is applied, so a macro cannot smuggle
// malformed pragma text past the check.
TEST(PragmaMacroInput, MacroSuppliesMalformedText_Rejected) {
  PreprocFixture f;
  Preprocess("`define MY_BAD a b\n`pragma my_pragma `MY_BAD\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PragmaMacroInput, MacroSuppliesNonIdentifierName_Rejected) {
  PreprocFixture f;
  Preprocess("`define PNAME 123\n`pragma `PNAME\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
