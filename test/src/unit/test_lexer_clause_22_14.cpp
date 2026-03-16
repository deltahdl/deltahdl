#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(KeywordVersionLexing, KeywordVersionMarker_RestoresToDefault) {
  std::string input;
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer13642001));
  input += '\n';
  input += "logic ";
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer18002023));
  input += '\n';
  input += "logic";
  auto tokens = Lex(input);
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwLogic);
}

TEST(KeywordVersionLexing, ParseKeywordVersion_ValidVersions) {
  struct Case {
    const char* input;
    KeywordVersion expected;
  };
  const Case kCases[] = {
      {"1364-1995", KeywordVersion::kVer13641995},
      {"1364-2001", KeywordVersion::kVer13642001},
      {"1364-2001-noconfig", KeywordVersion::kVer13642001Noconfig},
      {"1364-2005", KeywordVersion::kVer13642005},
      {"1800-2005", KeywordVersion::kVer18002005},
      {"1800-2009", KeywordVersion::kVer18002009},
      {"1800-2012", KeywordVersion::kVer18002012},
      {"1800-2017", KeywordVersion::kVer18002017},
      {"1800-2023", KeywordVersion::kVer18002023},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(ParseKeywordVersion(c.input), std::optional(c.expected))
        << c.input;
  }
}

TEST(KeywordVersionLexing, ParseKeywordVersion_Invalid) {
  EXPECT_FALSE(ParseKeywordVersion("bogus").has_value());
  EXPECT_FALSE(ParseKeywordVersion("").has_value());
}

TEST(KeywordVersionLexing, LookupKeyword_ReturnsKindForCurrentVersion) {
  auto result = LookupKeyword("logic", KeywordVersion::kVer18002023);
  ASSERT_TRUE(result.has_value());
  EXPECT_EQ(*result, TokenKind::kKwLogic);
}

TEST(KeywordVersionLexing, LookupKeyword_ReturnsNulloptForOlderVersion) {
  auto result = LookupKeyword("logic", KeywordVersion::kVer13642001);
  EXPECT_FALSE(result.has_value());
}

TEST(KeywordVersionLexing, LookupKeyword_NonKeywordReturnsNullopt) {
  auto result = LookupKeyword("my_ident", KeywordVersion::kVer18002023);
  EXPECT_FALSE(result.has_value());
}

TEST(KeywordVersionLexing, MarkerAtInputStart) {
  std::string input;
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer13641995));
  input += '\n';
  input += "module m; endmodule";
  auto tokens = Lex(input);
  bool found_module = false;
  for (const auto& tok : tokens) {
    if (tok.text == "module") {
      EXPECT_EQ(tok.kind, TokenKind::kKwModule);
      found_module = true;
    }
  }
  EXPECT_TRUE(found_module);
}

TEST(KeywordVersionLexing, ConsecutiveMarkersSwitchVersion) {
  std::string input;
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer13641995));
  input += '\n';
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer18002023));
  input += '\n';
  input += "logic";
  auto tokens = Lex(input);
  bool found_logic = false;
  for (const auto& tok : tokens) {
    if (tok.text == "logic") {
      EXPECT_EQ(tok.kind, TokenKind::kKwLogic);
      found_logic = true;
    }
  }
  EXPECT_TRUE(found_logic);
}

}  // namespace
