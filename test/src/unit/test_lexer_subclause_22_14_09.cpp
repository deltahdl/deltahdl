#include <gtest/gtest.h>

#include <cstddef>

#include "lexer/keywords.h"
#include "model_keyword_table_sweeps.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1800_2017_IncludesAllPriorVersions) {
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(
      LookupKeyword("automatic", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("uwire", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(
      LookupKeyword("checker", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002017).has_value());
}

TEST(Lexer, KeywordVersion_1800_2023_IncludesAllPriorVersions) {
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("automatic", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("uwire", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("checker", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002023).has_value());
}

TEST(Lexer, KeywordVersion_1800_2017_And_2023_AddNoNewKeywords) {
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002012).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002023).has_value());

  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer18002012).has_value());
  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer18002017).has_value());
  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer18002023).has_value());
}

TEST(Lexer, KeywordVersion_1800_2017_And_2023_ReserveEveryWordOfTheSixTables) {
  size_t swept = 0;
  for (const auto& table :
       {kVerilog1995KeywordSweep, kVerilog2001AddedKeywordSweep,
        kVerilog2005AddedKeywordSweep, kSystemVerilog2005AddedKeywordSweep,
        kSystemVerilog2009AddedKeywordSweep,
        kSystemVerilog2012AddedKeywordSweep}) {
    for (size_t i = 0; i < table.count; ++i) {
      const char* word = table.words[i];
      auto in_2012 = LookupKeyword(word, KeywordVersion::kVer18002012);
      ASSERT_TRUE(in_2012.has_value()) << word;
      if (!in_2012.has_value()) continue;
      for (auto version :
           {KeywordVersion::kVer18002017, KeywordVersion::kVer18002023}) {
        auto here = LookupKeyword(word, version);
        ASSERT_TRUE(here.has_value()) << word;
        if (!here.has_value()) continue;
        EXPECT_EQ(*here, *in_2012) << word;
      }
      ++swept;
    }
  }
  EXPECT_EQ(swept, 248u);
}

TEST(Lexer, KeywordVersion_1800_2017_And_2023_ReserveNoWordOutsideTheTables) {
  const char* const kNotWords[] = {
      "Module",     "MODULE",        "Soft",          "LOGIC",
      "modules",    "module_",       "_module",       "endmodules",
      "softly",     "soft_",         "nettypes",      "net_type",
      "implement",  "interconnects", "checkers",      "uwires",
      "endnettype", "endimplements", "my_signal",     "user_signal",
      "elsif",      "elif",          "foreachs",      "unique1",
      "priority_",  "constraintx",   "endinterface_", "classes",
  };
  for (const char* word : kNotWords) {
    for (auto version :
         {KeywordVersion::kVer18002017, KeywordVersion::kVer18002023}) {
      EXPECT_FALSE(LookupKeyword(word, version).has_value()) << word;
    }
  }
}

}  // namespace
