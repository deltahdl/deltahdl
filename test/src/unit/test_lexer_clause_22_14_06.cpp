#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1800_2005_LogicIsKeyword) {
  auto kw = LookupKeyword("logic", KeywordVersion::kVer18002005);
  EXPECT_EQ(kw, std::optional(TokenKind::kKwLogic));
}

TEST(Lexer, KeywordVersion_1800_2005_AllAdditionalKeywordsRecognized) {
  const char* kTable22_4[] = {
      "alias",       "always_comb",   "always_ff",    "always_latch",
      "assert",      "assume",        "before",       "bind",
      "bins",        "binsof",        "bit",          "break",
      "byte",        "chandle",       "class",        "clocking",
      "const",       "constraint",    "context",      "continue",
      "cover",       "covergroup",    "coverpoint",   "cross",
      "dist",        "do",            "endclass",     "endclocking",
      "endgroup",    "endinterface",  "endpackage",   "endprogram",
      "endproperty", "endsequence",   "enum",         "expect",
      "export",      "extends",       "extern",       "final",
      "first_match", "foreach",       "forkjoin",     "iff",
      "ignore_bins", "illegal_bins",  "import",       "inside",
      "int",         "interface",     "intersect",    "join_any",
      "join_none",   "local",         "logic",        "longint",
      "matches",     "modport",       "new",          "null",
      "package",     "packed",        "priority",     "program",
      "property",    "protected",     "pure",         "rand",
      "randc",       "randcase",      "randsequence", "ref",
      "return",      "sequence",      "shortint",     "shortreal",
      "solve",       "static",        "string",       "struct",
      "super",       "tagged",        "this",         "throughout",
      "timeprecision", "timeunit",    "type",         "typedef",
      "union",       "unique",        "var",          "virtual",
      "void",        "wait_order",    "wildcard",     "with",
      "within",
  };
  for (const char* kw : kTable22_4) {
    auto result = LookupKeyword(kw, KeywordVersion::kVer18002005);
    EXPECT_TRUE(result.has_value())
        << kw << " should be a keyword in 1800-2005";
  }
}

TEST(Lexer, KeywordVersion_1800_2005_IncludesEarlierKeywords) {
  // 1364-1995
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer18002005).has_value());
  EXPECT_TRUE(
      LookupKeyword("wire", KeywordVersion::kVer18002005).has_value());
  // 1364-2001
  EXPECT_TRUE(
      LookupKeyword("automatic", KeywordVersion::kVer18002005).has_value());
  EXPECT_TRUE(
      LookupKeyword("generate", KeywordVersion::kVer18002005).has_value());
  // 1364-2005
  EXPECT_TRUE(
      LookupKeyword("uwire", KeywordVersion::kVer18002005).has_value());
}

TEST(Lexer, KeywordVersion_1800_2005_LaterKeywordsNotRecognized) {
  // 1800-2009 additions
  EXPECT_FALSE(
      LookupKeyword("checker", KeywordVersion::kVer18002005).has_value());
  EXPECT_FALSE(
      LookupKeyword("accept_on", KeywordVersion::kVer18002005).has_value());
  EXPECT_FALSE(
      LookupKeyword("eventually", KeywordVersion::kVer18002005).has_value());
  // 1800-2012 additions
  EXPECT_FALSE(
      LookupKeyword("interconnect", KeywordVersion::kVer18002005).has_value());
  EXPECT_FALSE(
      LookupKeyword("soft", KeywordVersion::kVer18002005).has_value());
}

}  // namespace
