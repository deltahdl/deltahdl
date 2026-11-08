#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>

#include "lexer/keywords.h"
#include "lexer/token.h"
#include "model_keyword_table_sweeps.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

TEST(Lexer, OnlyTheExactSpecifierNamesTheVerilog2001List) {
  auto version = ParseKeywordVersion("1364-2001");
  ASSERT_TRUE(version.has_value());
  if (!version.has_value()) return;
  EXPECT_EQ(*version, KeywordVersion::kVer13642001);

  const char* const kNearMisses[] = {"1364-01",    "2001",      "1364-2001 ",
                                     " 1364-2001", "1364_2001", "1364-2002",
                                     "1364-20001", "1364200",   ""};
  for (const char* spec : kNearMisses) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << '"' << spec << "\" does not name this version";
  }
}

TEST(Lexer, Verilog2001AdditionsYieldTheirOwnToken) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywords), 21u);
  for (const char* kw : kVerilog2001AddedKeywords) {
    auto in_2001 = LookupKeyword(kw, KeywordVersion::kVer13642001);
    auto in_default = LookupKeyword(kw);
    ASSERT_TRUE(in_default.has_value()) << kw;
    ASSERT_TRUE(in_2001.has_value()) << kw << " is listed in Table 22-2";
    if (!in_default.has_value() || !in_2001.has_value()) continue;
    EXPECT_EQ(*in_2001, *in_default) << kw;
    EXPECT_NE(*in_2001, TokenKind::kIdentifier) << kw;
    EXPECT_FALSE(LookupKeyword(kw, KeywordVersion::kVer13641995).has_value())
        << kw << " is an addition, so the 1364-1995 list must not have it";
  }
}

TEST(Lexer, Verilog2001IncludesTheWholeVerilog1995List) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* kw : kVerilog1995Keywords) {
    auto in_2001 = LookupKeyword(kw, KeywordVersion::kVer13642001);
    auto in_default = LookupKeyword(kw);
    ASSERT_TRUE(in_default.has_value()) << kw;
    ASSERT_TRUE(in_2001.has_value()) << kw << " is carried over from 1364-1995";
    if (!in_default.has_value() || !in_2001.has_value()) continue;
    EXPECT_EQ(*in_2001, *in_default) << kw;
    EXPECT_NE(*in_2001, TokenKind::kIdentifier) << kw;
  }
}

TEST(Lexer, WordsOutsideTheVerilog2001ListAreNotReserved) {
  for (const auto& table :
       {kVerilog2005AddedKeywordSweep, kSystemVerilog2005AddedKeywordSweep,
        kSystemVerilog2009AddedKeywordSweep,
        kSystemVerilog2012AddedKeywordSweep}) {
    for (size_t i = 0; i < table.count; ++i) {
      const char* kw = table.words[i];
      EXPECT_FALSE(LookupKeyword(kw, KeywordVersion::kVer13642001).has_value())
          << kw << " is listed in neither Table 22-1 nor Table 22-2";
      EXPECT_TRUE(LookupKeyword(kw).has_value())
          << kw << " should still be reserved under the default list";
    }
  }
}

TEST(Lexer, OrdinaryIdentifierIsReservedByNoVerilog2001List) {
  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer13642001).has_value());
  EXPECT_FALSE(LookupKeyword("my_signal").has_value());
}

TEST(Lexer, WordsResemblingVerilog2001AdditionsAreNotReserved) {
  const char* const kNearMisses[] = {
      "GENVAR",     "Genvar",     "Localparam",  "SIGNED",
      "genvar_",    "generates",  "localparam1", "my_generate",
      "pulsestyle", "showcancel", "automatics",  "unsign",
  };
  for (const char* word : kNearMisses) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642001).has_value())
        << word << " is not one of Table 22-2's spellings";
    EXPECT_FALSE(LookupKeyword(word).has_value())
        << word << " is not reserved under the default list either";
  }
}

}  // namespace
