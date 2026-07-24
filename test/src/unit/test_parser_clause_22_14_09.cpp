#include "fixture_parser.h"

using namespace delta;

namespace {

// §22.14.9 defines the "1800-2017" and "1800-2023" version_specifiers. The
// begin_keywords/version_specifier grammar itself belongs to §22.14; these
// tests observe §22.14.9's rule — that each specifier reserves the identifiers
// of its standard, which include every prior version's keywords and add none of
// their own — end to end, driving real begin_keywords source through the
// preprocessor marker into the lexer and parser.

// §22.14.9 (includes all prior versions): the newest reserved word predates
// both specifiers — `soft` becomes reserved in IEEE Std 1800-2012 — and is
// carried forward unchanged. Used as a declaration identifier it is rejected
// under "1800-2017", proving the inherited reserved set is active in the
// region.
TEST(CompilerDirectiveParsing,
     BeginKeywords1800_2017_InheritedKeywordStaysReserved) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2017\"\n"
                              "module t;\n"
                              "  logic soft;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

// Same for "1800-2023": the inherited word `soft` stays reserved.
TEST(CompilerDirectiveParsing,
     BeginKeywords1800_2023_InheritedKeywordStaysReserved) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2023\"\n"
                              "module t;\n"
                              "  logic soft;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

// Contrast (proves the rejection above is version-driven, not unconditional):
// under "1800-2009" `soft` is not yet reserved, so the identical declaration
// parses. The 2017/2023 rejection is therefore the inherited 1800-2012
// reservation carried forward by §22.14.9, not a property of the default set.
TEST(CompilerDirectiveParsing, BeginKeywords1800_2009_SoftIsFreeIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2009\"\n"
                              "module t;\n"
                              "  logic soft;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

// §22.14.9 (adds no new reserved keywords): neither specifier promotes a
// previously free identifier to a keyword. An identifier that is not reserved
// at "1800-2012" stays a legal declaration name under "1800-2017" and
// "1800-2023" — the reserved set does not grow at the version boundary.
TEST(CompilerDirectiveParsing, BeginKeywords1800_2017_AddsNoNewKeyword) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2017\"\n"
                              "module t;\n"
                              "  logic user_signal;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1800_2023_AddsNoNewKeyword) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2023\"\n"
                              "module t;\n"
                              "  logic user_signal;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
