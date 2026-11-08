#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

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

TEST(PragmaDirective, KeywordAlone_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma requires a pragma_name", 1, "22.11"));
}

TEST(PragmaDirective, KeywordAloneNames22_11) {
  PreprocFixture f;
  Preprocess("`pragma\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma requires a pragma_name", 1, "22.11"));
}

TEST(PragmaDirective, OnlyWhitespaceAfterKeyword_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma   \n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma requires a pragma_name", 1, "22.11"));
}

TEST(PragmaDirective, TrailingComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1,\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaDirective, LeadingComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma , expr1\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaDirective, EmptyListElement_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1, , expr2\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaDirective, AdjacentExpressionsWithoutComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1 expr2\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaDirective, KeywordFlushAgainstName_IsMacroUsage) {
  PreprocFixture f;
  auto out = Preprocess("`define pragma_like wire w;\n`pragma_like\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire w;"), std::string::npos);
}

TEST(PragmaDirective, KeywordFlushAgainstDollarName_IsMacroUsage) {
  PreprocFixture f;
  auto out = Preprocess("`define pragma$x wire w;\n`pragma$x\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire w;"), std::string::npos);
}

TEST(PragmaDirective, ProducesNoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma my_pragma key = val, 42\n", f);
  EXPECT_TRUE(TrimAll(out).empty());
}

TEST(PragmaDirective, IndentedDirective_Accepted) {
  PreprocFixture f;
  auto out =
      Preprocess("module m;\n    `pragma my_pragma key = 1\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("endmodule"), std::string::npos);
}

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

TEST(PragmaName, UnderscoreLed_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma _my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaName, DigitsUnderscoreDollarTail_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma p1_a$b2\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaName, DigitLed_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma 123\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma pragma_name must be a simple identifier",
                            1, "22.11"));
}

TEST(PragmaName, String_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma \"my_pragma\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma pragma_name must be a simple identifier",
                            1, "22.11"));
}

TEST(PragmaName, DollarLed_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma $my_pragma\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(PragmaName, EscapedIdentifier_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma \\my_pragma \n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma pragma_name must be a simple identifier",
                            1, "22.11"));
}

TEST(PragmaName, SpelledLikeADirectiveKeyword_Accepted) {
  PreprocFixture f;
  auto out = Preprocess("`pragma define\nwire w;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(TrimAll(out), "wire w;");
}

TEST(PragmaName, ParenthesizedList_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma (a, b)\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma pragma_name must be a simple identifier",
                            1, "22.11"));
}

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

TEST(PragmaExpression, EqualsWithoutKeyword_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma = val1\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaExpression, KeywordWithoutValue_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma key1 =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaExpression, DoubledEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma key1 = = val1\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaExpression, ChainedEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma a = b = c\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaKeyword, StringOnLeftOfEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma \"key\" = val1\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaKeyword, EscapedIdentifierOnLeftOfEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma \\key$1 = val1\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaKeyword, ParenthesizedListOnLeftOfEquals_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, b) = val1\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaValue, SizedBasedNumber_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma width = 8'hFF\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

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

TEST(PragmaValue, RealNumberWithSignedExponent_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma ratio = 1.5e-3\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, LeadingSign_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma offset = -5\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
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

TEST(PragmaValue, StringContainingListPunctuation_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"a, b = (c)\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, TripleQuotedString_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"\"\"a \"quoted\" phrase\"\"\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaValue, UnterminatedTripleQuotedString_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"\"\"never closed\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(PragmaValue, SimpleIdentifier_Accepted) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma mode = fast\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

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

TEST(PragmaValue, EmptyParentheses_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma ()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaValue, UnbalancedOpenParen_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, b\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaValue, UnbalancedNestedParen_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, (b, c)\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaValue, StrayCloseParen_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma a)\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaValue, ParenthesizedListMissingComma_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a b)\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(PragmaValue, UnterminatedString_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"unterminated\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(PragmaValue, ExponentSignsInBothCases_Accepted) {
  for (const char* value : {"1e+5", "1E-5", "2.5E+1"}) {
    PreprocFixture f;
    Preprocess(std::string("`pragma my_pragma ratio = ") + value + "\n", f);
    EXPECT_FALSE(f.diag.HasErrors()) << value;
  }
}

TEST(PragmaValue, SignInsideANumber_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma offset = 1-2\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(PragmaValue, TickOpeningNoNumber_Rejected) {
  for (const char* value : {"'", "'(1)"}) {
    PreprocFixture f;
    Preprocess(std::string("`pragma my_pragma v = ") + value + "\n", f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "`pragma directive contains an illegal token", 1,
                              "22.11"))
        << value;
  }
}

TEST(PragmaValue, StringEndingInABackslash_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma note = \"abc\\\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(PragmaValue, LoneBackslash_Rejected) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma v = \\ , w\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(PragmaValue, SlashOpeningNoComment_Rejected) {
  for (const char* tail : {"/", "/x"}) {
    PreprocFixture f;
    Preprocess(std::string("`pragma my_pragma v = 1 ") + tail + "\n", f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "`pragma directive contains an illegal token", 1,
                              "22.11"))
        << tail;
  }
}

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

TEST(PragmaConditional, MalformedPragmaInActiveBranchIsDiagnosed) {
  PreprocFixture f;
  Preprocess(
      "`define ON\n"
      "`ifdef ON\n"
      "`pragma 123\n"
      "`endif\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma pragma_name must be a simple identifier",
                            3, "22.11"));
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

TEST(PragmaMacroInput, MacroSuppliesMalformedText_Rejected) {
  PreprocFixture f;
  Preprocess("`define MY_BAD a b\n`pragma my_pragma `MY_BAD\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 2,
                            "22.11"));
}

TEST(PragmaMacroInput, MacroSuppliesNonIdentifierName_Rejected) {
  PreprocFixture f;
  Preprocess("`define PNAME 123\n`pragma `PNAME\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma pragma_name must be a simple identifier",
                            2, "22.11"));
}

TEST(Preprocessor, EncryptingHalfRefusesALineTheGrammarRejects) {
  struct Case {
    std::string_view line;
    std::string_view message;
    std::string_view stray;
  };
  for (const Case& c : {
           Case{"`pragma protect data_keyowner=\"acme\n",
                "`pragma directive contains an illegal token", "=\"acme"},
           Case{"`pragma protect data_keyname=\"k1\n",
                "`pragma directive contains an illegal token", "\"k1"},
           Case{"`pragma protect encoding=(enctype=\"base64\", line_length=)\n",
                "malformed pragma_expression after pragma_name", "\"base64\""},
           Case{"`pragma protect encoding=(enctype=\"base64\", "
                "line_length=8))\n",
                "malformed pragma_expression after pragma_name", "\"base64\""},
       }) {
    std::string src = "`pragma protect begin\n";
    src.append(c.line).append("module m; endmodule\n`pragma protect end\n");
    SourceManager mgr;
    DiagEngine diag(mgr);
    std::string envelope = EncryptEnvelopes(src, "k", ProtectKeyList(), &diag,
                                            mgr.AddFile("<test>", src));
    EXPECT_TRUE(ReportedError(diag.Diagnostics(), c.message, 2, "22.11"))
        << c.line;
    EXPECT_EQ(envelope.find(c.stray), std::string::npos) << envelope;
  }
  std::string src = "`pragma protect data_keyowner=\"acme\n";
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_EQ(EncryptEnvelopes(src, "k", ProtectKeyList(), &diag,
                             mgr.AddFile("<test>", src)),
            src);
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
  std::string usage = "`pragma protect `NAMES\n";
  DiagEngine quiet(mgr);
  EncryptEnvelopes(usage, "k", ProtectKeyList(), &quiet,
                   mgr.AddFile("<usage>", usage));
  EXPECT_FALSE(quiet.HasErrors());
}

}  // namespace
