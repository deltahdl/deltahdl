#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_viewport.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_viewport.h"

using namespace delta;

// §34.5.32.1 Syntax, for the viewport protect pragma keyword.
//
// The subclause is one line:
//
//   viewport = ( object = <string> , access = <string> )
//
// It settles the spelling and nothing else. §34.5.32.2 says what an expression
// written that way does, and test_preprocessor_subclause_34_05_32_02.cpp reads
// that; what this file varies is the writing, holding everything else fixed.
//
// The spelling is read by ParseProtectViewport in
// src/preprocessor/protect_viewport.cpp, and a value written any other way is
// reported by Preprocessor::ApplyViewport in
// src/preprocessor/preprocessor_protect_viewport.cpp.
//
// Every source here opens an envelope and leaves it open, because §34.5.32.2
// has an expression describe an object of the envelope in force and reports one
// standing where no envelope does. Holding the envelope open is what keeps a
// case about the spelling from being answered by that other rule.

struct ProtectViewportSyntaxTest : ::testing::Test {
 protected:
  std::string Preprocess(const std::string& src) {
    auto fid = mgr_.AddFile("<test>", src);
    Preprocessor pp(mgr_, diag_, config_);
    return pp.Preprocess(fid);
  }

  SourceManager mgr_;
  DiagEngine diag_{mgr_};
  PreprocConfig config_;
};

namespace {

// The object a source names and the access it asks for it. Both hold
// characters no keyword is spelled with, so a value read back is the one the
// directive wrote rather than a name that happened to be lying about.
constexpr std::string_view kObject = "top.dut.mem";
constexpr std::string_view kAccess = "read-only";

// The expression that opens a decryption envelope, which every source below
// stands inside.
constexpr std::string_view kOpensEnvelope = "`pragma protect begin_protected\n";

// The message Preprocessor::ApplyViewport reports a value not written in this
// subclause's spelling with.
constexpr std::string_view kNotTheSpelling =
    "viewport expression is written as an object and an access";

// The line of a source built by InsideAnEnvelope that a report about its
// directive stands at. The envelope is opened on the first line, so the
// directive under test is on the second.
constexpr uint32_t kDirectiveLine = 2;

// A source opening an envelope and then writing `expressions` on a protect
// pragma directive of its own.
std::string InsideAnEnvelope(std::string_view expressions) {
  std::string src(kOpensEnvelope);
  src.append(ProtectDirective(expressions));
  return src;
}

// A viewport expression whose parentheses hold `items`.
std::string ViewportWriting(std::string_view items) {
  std::string expression = "viewport = ( ";
  expression.append(items).append(" )");
  return expression;
}

// The two names written against the two values, as §34.5.32.1 writes them.
std::string BothNames() {
  std::string items = "object = \"";
  items.append(kObject).append("\" , access = \"").append(kAccess).append("\"");
  return items;
}

// Whether a reading of `expressions` turned the value away as a spelling
// §34.5.32.1 does not define, naming the report rather than counting one.
::testing::AssertionResult NotTheSpelling(std::string_view expressions) {
  ReadingViewports reading(InsideAnEnvelope(expressions));
  return ReportedError(reading.diag.Diagnostics(), kNotTheSpelling,
                       kDirectiveLine, "34.5.32.1");
}

// ---------------------------------------------------------------------------
// The spelling the subclause defines.
// ---------------------------------------------------------------------------

// §34.5.32.1 as written: the keyword, an equals, and a parenthesized list
// naming an object and an access against strings. The two values come back as
// the directive wrote them, without the quotation marks §22.5.1 spelled a
// string with.
TEST(ProtectViewportSyntax, TheParenthesizedObjectAndAccessIsTheSpelling) {
  ReadingViewports reading(InsideAnEnvelope(ViewportWriting(BothNames())));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

// The directive line goes away like any other protect pragma directive, and
// the text around it does not. This says which line the reading consumed; it
// says nothing about the spelling, every directive line going away whatever it
// wrote, which is why it is the only case here that reads the produced text.
TEST_F(ProtectViewportSyntaxTest,
       ViewportDirectiveStrippedSurroundingTextKept) {
  std::string result =
      Preprocess("module m;\n" + std::string(kOpensEnvelope) +
                 ViewportOf(kObject, kAccess) +
                 "`pragma protect end_protected\n" + "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find(kObject), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// §22.5.1 writes a directive's expressions as a list, and the value is read
// the same way wherever in that list the keyword stands. A reading that took
// the value off the first expression alone would have the keyword mean
// something different for being written second.
TEST(ProtectViewportSyntax, TheSpellingIsItselfBesideAnotherExpression) {
  ReadingViewports reading(
      InsideAnEnvelope("author=\"acme\", " + ViewportWriting(BothNames())));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

// §22.5.1 spells the value as a list of pragma expressions, which name what
// they carry rather than standing at a position. So the two names are read by
// name, and a text writing the access first has written the same value.
TEST(ProtectViewportSyntax, TheTwoNamesAreReadInEitherOrder) {
  std::string items = "access = \"";
  items.append(kAccess).append("\" , object = \"").append(kObject).append("\"");
  ReadingViewports reading(InsideAnEnvelope(ViewportWriting(items)));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

// A name §34.5.32.1 does not write qualifies the value with something the
// subclause says nothing about, so nothing is taken from it and the two names
// it does write are still there. Without this the cases above would hold of a
// reading that required the list to be exactly two expressions long.
TEST(ProtectViewportSyntax, AThirdNameLeavesTheTwoTheSubclauseWrites) {
  ReadingViewports reading(InsideAnEnvelope(
      ViewportWriting(BothNames() + " , retention = \"forever\"")));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

// ---------------------------------------------------------------------------
// The <string> the subclause writes each name against.
// ---------------------------------------------------------------------------

// A string may hold a space, and the value is the whole of what stands between
// the quotation marks. A reading that took the value up to the first space
// would have half of it.
TEST(ProtectViewportSyntax, AValueHoldingASpaceIsOneValue) {
  ReadingViewports reading(std::string(kOpensEnvelope) +
                           ViewportOf("top.dut.mem array", kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, "top.dut.mem array");
}

// A string may hold the comma the list is written with, and it is content of
// the value rather than the end of an expression. This is the case that says
// the list is split at its own level: a reading splitting on every comma would
// find three expressions here and neither of the two names against a string.
TEST(ProtectViewportSyntax, AValueHoldingACommaIsStillOneValue) {
  ReadingViewports reading(std::string(kOpensEnvelope) +
                           ViewportOf(kObject, "read, write"));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, "read, write");
}

// A string may hold nothing at all, and a name written against an empty string
// is still written against a string. The expression is the spelling the
// subclause defines, whatever §34.5.32.2 goes on to make of an object with no
// name.
TEST(ProtectViewportSyntax, AnEmptyStringIsAValueTheSpellingAdmits) {
  ReadingViewports reading(std::string(kOpensEnvelope) +
                           ViewportOf("", kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_TRUE(reading.Viewports().front().object.empty());
}

// ---------------------------------------------------------------------------
// Writings that are not that spelling.
// ---------------------------------------------------------------------------

// §34.5.32.1 writes a value against the keyword, so the keyword standing alone
// is not the expression the subclause defines and describes nothing.
TEST(ProtectViewportSyntax, TheKeywordStandingAloneIsReported) {
  EXPECT_TRUE(NotTheSpelling("viewport"));
}

// §22.5.1 spells a pragma_value as one written thing or as a parenthesized
// list of further expressions, and §34.5.32.1 writes the list. A single string
// written against the keyword names no object and no access, however much it
// reads like the object a producer meant.
TEST(ProtectViewportSyntax, ASingleStringAgainstTheKeywordIsReported) {
  EXPECT_TRUE(NotTheSpelling("viewport=\"" + std::string(kObject) + "\""));
}

// §34.5.32.1 writes both names. A list naming only the access describes no
// object, so there is nothing for the access it asks to be permitted for.
TEST(ProtectViewportSyntax, AListLeavingTheObjectOutIsReported) {
  EXPECT_TRUE(NotTheSpelling(
      ViewportWriting("access = \"" + std::string(kAccess) + "\"")));
}

// The other name left out, which is what makes the case above about both names
// being required rather than about the object alone. A list naming only the
// object asks that nothing in particular be permitted for it.
TEST(ProtectViewportSyntax, AListLeavingTheAccessOutIsReported) {
  EXPECT_TRUE(NotTheSpelling(
      ViewportWriting("object = \"" + std::string(kObject) + "\"")));
}

// §34.5.32.1 writes each name against a <string>, and §22.5.1 gives a
// pragma_value three other spellings. An identifier written against the object
// is one of those three and is not the string the subclause writes.
TEST(ProtectViewportSyntax, AnObjectWrittenBareIsReported) {
  EXPECT_TRUE(NotTheSpelling(ViewportWriting("object = top , access = \"" +
                                             std::string(kAccess) + "\"")));
}

// The same of the other name, written as the remaining spelling of a
// pragma_value: a number is not a string either. Two names and two spellings
// are varied across these two cases, a reading that looked for quotation marks
// against one name and not the other being what either alone would pass.
TEST(ProtectViewportSyntax, AnAccessWrittenAsANumberIsReported) {
  EXPECT_TRUE(NotTheSpelling(ViewportWriting(
      "object = \"" + std::string(kObject) + "\" , access = 3")));
}

// ---------------------------------------------------------------------------
// Names that are not this keyword.
// ---------------------------------------------------------------------------

// §34.5.32.1 spells one name, and a name that merely opens with those
// characters is a different one. §34.4 tabulates no such name, so a text
// writing it has written a keyword the protect pragma does not reserve: there
// is nothing to describe an object with and nothing to report about the
// spelling of a value.
TEST(ProtectViewportSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadingViewports reading(
      InsideAnEnvelope("viewports = ( " + BothNames() + " )"));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
  EXPECT_FALSE(reading.diag.HasErrors());
}

// §22.5.1 spells a pragma_keyword as a simple identifier, and §5.6.1 makes an
// escaped identifier a different spelling from the simple one. So the escaped
// spelling names a keyword §34.4 does not tabulate, for the same reason and
// with the same consequence as the longer name above.
//
// It is written standing alone, which is what says the name rather than the
// value decided this: the same characters spelled simply and standing alone
// are reported by TheKeywordStandingAloneIsReported above, and here they are
// not reported at all.
TEST(ProtectViewportSyntax, AnEscapedSpellingOfTheKeywordIsNotIt) {
  ReadingViewports reading(InsideAnEnvelope("\\viewport"));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
  EXPECT_FALSE(reading.diag.HasErrors());
}

}  // namespace
