#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(KeywordVersionLexing, KeywordVersionMarkerRestoresToDefault) {
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

TEST(KeywordVersionLexing, ParseKeywordVersionAcceptsEverySpecifier) {
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

TEST(KeywordVersionLexing, LookupKeywordReturnsKindForSelectedVersion) {
  auto result = LookupKeyword("logic", KeywordVersion::kVer18002023);
  ASSERT_TRUE(result.has_value());
  EXPECT_EQ(result, std::optional(TokenKind::kKwLogic));
}

TEST(KeywordVersionLexing, LookupKeywordFindsNothingForOlderVersion) {
  auto result = LookupKeyword("logic", KeywordVersion::kVer13642001);
  EXPECT_FALSE(result.has_value());
}

TEST(KeywordVersionLexing, LookupKeywordFindsNothingForOrdinaryIdentifier) {
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

// §22.14: when no `begin_keywords directive is in effect (no version marker
// precedes the source), the lexer applies the implementation's default reserved
// keyword set. This implementation's default is IEEE 1800-2023, so a word that
// is reserved there lexes as a keyword with no marker present at all.
TEST(KeywordVersionLexing, NoDirectiveUsesDefaultKeywordSet) {
  auto tokens = Lex("logic");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
}

// Syntax 22-10 lists the version_specifier alternatives exhaustively. Strings
// that are close to one of them but not equal to it are not alternatives of
// that production, so they must not resolve to a version; `begin_keywords
// reports such a specifier as an error precisely because this returns nothing.
TEST(KeywordVersionLexing, ParseKeywordVersionRejectsNearMisses) {
  const char* kRejected[] = {
      "",                    // no specifier text at all
      "bogus",               // unrelated word
      "1800-2020",           // a year the production does not list
      "1364-2000",           // ditto, on the 1364 side
      "1800",                // standard number with no year
      "2023",                // year with no standard number
      "1800-2023-noconfig",  // the noconfig suffix belongs to 1364-2001 only
      "1364-2005-noconfig",
      "1800_2023",
      "IEEE1800-2023",
      " 1800-2023",
      "1800-2023 ",
  };
  for (const char* spec : kRejected) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value()) << spec;
  }
}

// §22.14: the selected reserved word list stays in effect for all the source
// that follows, not merely for the next token. Under the 1364-1995 list every
// later-standard reserved word downstream of the marker is still an ordinary
// identifier, several tokens and several lines further on.
TEST(KeywordVersionLexing, MarkerAppliesToAllFollowingTokens) {
  std::string input;
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer13641995));
  input += '\n';
  input += "logic bit;\n";
  input += "byte interface;\n";
  input += "shortint longint;\n";

  auto tokens = Lex(input);
  size_t identifiers = 0;
  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kIdentifier) ++identifiers;
    EXPECT_NE(tok.kind, TokenKind::kKwLogic) << tok.text;
  }
  EXPECT_EQ(identifiers, 6u);
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
