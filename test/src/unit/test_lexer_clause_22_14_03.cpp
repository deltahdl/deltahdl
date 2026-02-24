// §22.14.3: IEEE Std 1364-2001 keywords

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

// --- Keyword version tests (IEEE 1800-2023 §22.14) ---
TEST(Lexer, KeywordVersion_1364_2001_LogicIsIdentifier) {
  // "logic" was introduced in 1800-2005, not a keyword in 1364-2001.
  auto kw = LookupKeyword("logic", KeywordVersion::kVer13642001);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, KeywordVersion_1364_1995_AutomaticIsNotKeyword) {
  // "automatic" was introduced in 1364-2001.
  auto kw = LookupKeyword("automatic", KeywordVersion::kVer13641995);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, KeywordVersionMarker_SwitchesVersion) {
  // Build input: marker for 1364-2001, then "logic".
  // The lexer should tokenize "logic" as an identifier, not a keyword.
  std::string input;
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer13642001));
  input += '\n';
  input += "logic";
  auto tokens = Lex(input);
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "logic");
}

}  // namespace
