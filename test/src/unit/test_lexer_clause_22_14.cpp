// §22.14: `begin_keywords, `end_keywords

#include <gtest/gtest.h>
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string &src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

namespace {

TEST(Lexer, KeywordVersionMarker_RestoresToDefault) {
  // marker 1364-2001, "logic", marker 1800-2023, "logic"
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

TEST(Lexer, ParseKeywordVersion_ValidVersions) {
  // §22.14: all nine version specifiers
  struct Case {
    const char *input;
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
  for (const auto &c : kCases) {
    EXPECT_EQ(ParseKeywordVersion(c.input), std::optional(c.expected))
        << c.input;
  }
}

TEST(Lexer, ParseKeywordVersion_Invalid) {
  EXPECT_FALSE(ParseKeywordVersion("bogus").has_value());
  EXPECT_FALSE(ParseKeywordVersion("").has_value());
}

}  // namespace
