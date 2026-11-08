#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_begin_keywords_token_kind.h"
#include "lexer/keywords.h"
#include "lexer/token.h"

using namespace delta;

namespace {

struct Verilog2001KeywordEntry {
  const char* word;
  TokenKind kind_under_2001;
  bool dropped_by_noconfig;
};

constexpr Verilog2001KeywordEntry kVerilog2001AddedKeywordEntries[] = {
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

TEST(KeywordVersionPreprocessing, NoconfigDropsExactlyTheTenNamedWords) {
  for (const auto& entry : kVerilog2001AddedKeywordEntries) {
    ExpectBeginKeywordsTokenKind("1364-2001-noconfig", entry.word,
                                 entry.dropped_by_noconfig
                                     ? TokenKind::kIdentifier
                                     : entry.kind_under_2001);
  }
}

TEST(KeywordVersionPreprocessing, Verilog2001KeepsItsAdditionsReserved) {
  for (const auto& entry : kVerilog2001AddedKeywordEntries) {
    ExpectBeginKeywordsTokenKind("1364-2001", entry.word,
                                 entry.kind_under_2001);
  }
}

TEST(KeywordVersionPreprocessing, NoconfigKeepsInheritedKeywords) {
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "module",
                               TokenKind::kKwModule);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "reg", TokenKind::kKwReg);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "wire",
                               TokenKind::kKwWire);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "always",
                               TokenKind::kKwAlways);
}

TEST(KeywordVersionPreprocessing, NoconfigLexesLaterWordsAsIdentifiers) {
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "uwire",
                               TokenKind::kIdentifier);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "logic",
                               TokenKind::kIdentifier);
  ExpectBeginKeywordsTokenKind("1364-2001-noconfig", "interface",
                               TokenKind::kIdentifier);
}

}  // namespace
