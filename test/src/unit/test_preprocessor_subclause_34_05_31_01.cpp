#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "helpers_protect_keyword_value.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `reset` protect pragma keyword (§34.5.31.1).
// The syntax block defines the keyword as the bare word `reset` with no
// arguments. Protect pragmas are processed at the preprocessor stage, where the
// generic `pragma` handler recognizes the keyword and consumes the directive
// line.
struct ProtectResetSyntaxTest : ::testing::Test {
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

// The bare `reset` keyword is accepted and the directive line is stripped.
TEST_F(ProtectResetSyntaxTest, PragmaProtectResetConsumed) {
  auto result = Preprocess("`pragma protect reset\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("reset"), std::string::npos);
}

// Only the reset directive line is removed; neighboring source text survives,
// confirming it is the reset keyword line that the pragma path consumes.
TEST_F(ProtectResetSyntaxTest, ResetDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect reset\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two cases above observe the directive line going away, which any protect
// pragma directive does whatever it writes, so a name §34.5.31.1 does not
// define brings the line's disappearance about just as readily. What §34.5.31.1
// defines is the spelling: the keyword standing alone, with nothing written
// against it. The cases below vary that spelling and nothing else, and read
// back the value a keyword written ahead of it is left holding.

// A provider named where §34.5.10.1 writes one. It is what the cases below read
// back: a text that crossed the expression §34.5.31.1 defines has the name at
// its default again, and a text that wrote a spelling the subclause does not
// define still has the provider it named.
constexpr std::string_view kProvider = "Meridian Aerospace";

// A key of that provider, named where §34.5.12.1 writes one. It is read back
// only by the case writing two expressions on one directive, which needs a
// second keyword to ask about.
constexpr std::string_view kProvidersKey = "meridian-2031";

// A protect pragma directive writing `expressions`, spelled as they stand here.
std::string Directive(std::string_view expressions) {
  std::string text = "`pragma protect ";
  text.append(expressions).append("\n");
  return text;
}

// The directive naming the provider the cases read back.
std::string NamesTheProvider() {
  std::string expression = "data_keyowner=\"";
  expression.append(kProvider).append("\"");
  return Directive(expression);
}

// §34.5.31.1 writes the keyword standing alone, and §34.5.31.2 has it restore
// what a reset pragma directive naming protect restores: every protect pragma
// keyword back at the value it had before any text was read.
TEST(ProtectResetSyntax, TheKeywordStandingAloneIsTheSpellingThatRestores) {
  EXPECT_TRUE(ReadKeywordScope(NamesTheProvider() + Directive(kResetKeyword))
                  .ValueOf(kDataKeyownerKeyword)
                  .defaulted);
}

// §34.5.31.1 writes nothing against the keyword, so the same name carrying a
// pragma_value is written in a spelling the subclause does not define and
// restores nothing. The provider named before it is still the one in effect.
TEST(ProtectResetSyntax, AValueWrittenAgainstTheKeywordRestoresNothing) {
  EXPECT_EQ(ReadKeywordScope(NamesTheProvider() + Directive("reset=\"now\""))
                .ValueOf(kDataKeyownerKeyword)
                .value,
            kProvider);
}

// §22.5.1 gives a pragma_value a parenthesized spelling as well, and that
// spelling is no more the bare keyword §34.5.31.1 defines than the quoted one
// is. Writing it therefore restores nothing either, which is what makes the
// case above about a value rather than about the characters one is spelled
// with.
TEST(ProtectResetSyntax, AListWrittenAgainstTheKeywordRestoresNothing) {
  EXPECT_EQ(
      ReadKeywordScope(NamesTheProvider() + Directive("reset=(all=\"yes\")"))
          .ValueOf(kDataKeyownerKeyword)
          .value,
      kProvider);
}

// §34.5.31.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer name has written a
// keyword §34.4 does not tabulate, so nothing is restored.
TEST(ProtectResetSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_EQ(ReadKeywordScope(NamesTheProvider() + Directive("resets"))
                .ValueOf(kDataKeyownerKeyword)
                .value,
            kProvider);
}

// §22.5.1 spells a pragma_keyword as a simple identifier, and §5.6.1 makes an
// escaped identifier a different spelling from the simple one. A text writing
// the escaped spelling has written a name §34.4 does not tabulate.
TEST(ProtectResetSyntax, AnEscapedSpellingOfTheKeywordIsNotIt) {
  EXPECT_EQ(ReadKeywordScope(NamesTheProvider() + Directive("\\reset"))
                .ValueOf(kDataKeyownerKeyword)
                .value,
            kProvider);
}

// §22.5.1 writes a directive's expressions as a list, and the keyword standing
// alone is that spelling wherever in the list it stands. §34.4 reads the list
// in the order it was written, so a keyword written after the reset is stated
// after it and is in effect where the reading stops.
TEST(ProtectResetSyntax, TheKeywordIsStillItselfBesideAnotherExpression) {
  std::string expressions = "reset, data_keyname=\"";
  expressions.append(kProvidersKey).append("\"");
  ReadKeywordScope scope(NamesTheProvider() + Directive(expressions));
  EXPECT_TRUE(scope.ValueOf(kDataKeyownerKeyword).defaulted);
  EXPECT_EQ(scope.ValueOf(kDataKeynameKeyword).value, kProvidersKey);
}

}  // namespace
