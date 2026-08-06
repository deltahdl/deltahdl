#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_begin_keywords_token_kind.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// Table 22-2 split the way this subclause splits it. The `kind` column is what
// the word lexes as under "1364-2001"; under this version the ten dropped ones
// lex as ordinary identifiers instead and the eleven kept ones do not change.
struct Table222Entry {
  const char* word;
  TokenKind kind_under_2001;
  bool dropped_by_noconfig;
};

constexpr Table222Entry kTable222[] = {
    {"automatic", TokenKind::kKwAutomatic, false},
    {"cell", TokenKind::kKwCell, true},
    {"config", TokenKind::kKwConfig, true},
    {"design", TokenKind::kKwDesign, true},
    {"endconfig", TokenKind::kKwEndconfig, true},
    {"endgenerate", TokenKind::kKwEndgenerate, false},
    {"generate", TokenKind::kKwGenerate, false},
    {"genvar", TokenKind::kKwGenvar, false},
    {"incdir", TokenKind::kKwIncdir, true},
    {"include", TokenKind::kKwInclude, true},
    {"instance", TokenKind::kKwInstance, true},
    {"liblist", TokenKind::kKwLiblist, true},
    {"library", TokenKind::kKwLibrary, true},
    {"localparam", TokenKind::kKwLocalparam, false},
    {"noshowcancelled", TokenKind::kKwNoshowcancelled, false},
    {"pulsestyle_ondetect", TokenKind::kKwPulsestyleOndetect, false},
    {"pulsestyle_onevent", TokenKind::kKwPulsestyleOnevent, false},
    {"showcancelled", TokenKind::kKwShowcancelled, false},
    {"signed", TokenKind::kKwSigned, false},
    {"unsigned", TokenKind::kKwUnsigned, false},
    {"use", TokenKind::kKwUse, true},
};

TEST(KeywordVersionPreprocessing, NoconfigRegionEmitsItsOwnVersionMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001-noconfig\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642001Noconfig);
}

// The marker this version emits is its own, distinct from the one the version
// it is defined in terms of emits. The exception can only reach the lexer if
// the two regions are told apart here first.
TEST(KeywordVersionPreprocessing, NoconfigMarkerDiffersFromVerilog2001) {
  auto marker_for = [](const char* version) {
    PreprocFixture f;
    auto out = Preprocess(
        std::string("`begin_keywords \"") + version + "\"\nx\n`end_keywords\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors());
    auto pos = out.find(kKeywordMarker);
    EXPECT_NE(pos, std::string::npos);
    return pos == std::string::npos ? KeywordVersion::kVer18002023
                                    : static_cast<KeywordVersion>(out[pos + 1]);
  };

  EXPECT_NE(marker_for("1364-2001-noconfig"), marker_for("1364-2001"));
}

// The whole of Table 22-2, driven through a real `begin_keywords region and
// read back as tokens: the ten this subclause names come out of the region as
// ordinary identifiers, and the other eleven still come out as the keywords
// "1364-2001" made them. Sweeping the table rather than sampling it is what
// makes the exception, and not two convenient words, the thing observed.
TEST(KeywordVersionPreprocessing, NoconfigDropsExactlyTheTenNamedWords) {
  for (const auto& entry : kTable222) {
    ExpectBeginKeywordsTokenKind("1364-2001-noconfig", entry.word,
                                 entry.dropped_by_noconfig
                                     ? TokenKind::kIdentifier
                                     : entry.kind_under_2001);
  }
}

// The same sweep against the version this one is defined from, which is what
// makes each of the ten an *exception* rather than a word that was never
// reserved: under "1364-2001" every entry of the table lexes as its keyword.
TEST(KeywordVersionPreprocessing, Verilog2001KeepsItsAdditionsReserved) {
  for (const auto& entry : kTable222) {
    ExpectBeginKeywordsTokenKind("1364-2001", entry.word,
                                 entry.kind_under_2001);
  }
}

// The inherited list is untouched by the exception, so words Table 22-1 names
// still arrive at the lexer as keywords inside a region of this version.
TEST(KeywordVersionPreprocessing, NoconfigKeepsInheritedKeywords) {
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "module",
                               TokenKind::kKwModule);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "reg", TokenKind::kKwReg);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "wire",
                               TokenKind::kKwWire);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "always",
                               TokenKind::kKwAlways);
}

// The bound from above: this version reserves no more than "1364-2001" does,
// so a word a later list introduces reaches the lexer as an identifier.
TEST(KeywordVersionPreprocessing, NoconfigLexesLaterWordsAsIdentifiers) {
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "uwire",
                               TokenKind::kIdentifier);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "logic",
                               TokenKind::kIdentifier);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "interface",
                               TokenKind::kIdentifier);
}

}  // namespace
