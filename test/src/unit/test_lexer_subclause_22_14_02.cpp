#include <gtest/gtest.h>

#include <iterator>

#include "lexer/keywords.h"
#include "lexer/token.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

constexpr const char* kWordsAddedAfterVerilog1995[] = {
    "accept_on",
    "alias",
    "always_comb",
    "always_ff",
    "always_latch",
    "assert",
    "assume",
    "automatic",
    "before",
    "bind",
    "bins",
    "binsof",
    "bit",
    "break",
    "byte",
    "cell",
    "chandle",
    "checker",
    "class",
    "clocking",
    "config",
    "const",
    "constraint",
    "context",
    "continue",
    "cover",
    "covergroup",
    "coverpoint",
    "cross",
    "design",
    "dist",
    "do",
    "endchecker",
    "endclass",
    "endclocking",
    "endconfig",
    "endgenerate",
    "endgroup",
    "endinterface",
    "endpackage",
    "endprogram",
    "endproperty",
    "endsequence",
    "enum",
    "eventually",
    "expect",
    "export",
    "extends",
    "extern",
    "final",
    "first_match",
    "foreach",
    "forkjoin",
    "generate",
    "genvar",
    "global",
    "iff",
    "ignore_bins",
    "illegal_bins",
    "implements",
    "implies",
    "import",
    "incdir",
    "include",
    "inside",
    "instance",
    "int",
    "interconnect",
    "interface",
    "intersect",
    "join_any",
    "join_none",
    "let",
    "liblist",
    "library",
    "local",
    "localparam",
    "logic",
    "longint",
    "matches",
    "modport",
    "nettype",
    "new",
    "nexttime",
    "noshowcancelled",
    "null",
    "package",
    "packed",
    "priority",
    "program",
    "property",
    "protected",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "pure",
    "rand",
    "randc",
    "randcase",
    "randsequence",
    "ref",
    "reject_on",
    "restrict",
    "return",
    "s_always",
    "s_eventually",
    "s_nexttime",
    "s_until",
    "s_until_with",
    "sequence",
    "shortint",
    "shortreal",
    "showcancelled",
    "signed",
    "soft",
    "solve",
    "static",
    "string",
    "strong",
    "struct",
    "super",
    "sync_accept_on",
    "sync_reject_on",
    "tagged",
    "this",
    "throughout",
    "timeprecision",
    "timeunit",
    "type",
    "typedef",
    "union",
    "unique",
    "unique0",
    "unsigned",
    "until",
    "until_with",
    "untyped",
    "use",
    "uwire",
    "var",
    "virtual",
    "void",
    "wait_order",
    "weak",
    "wildcard",
    "with",
    "within",
};

TEST(Lexer, Verilog1995KeywordsYieldTheirOwnToken) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* kw : kVerilog1995Keywords) {
    auto in_1995 = LookupKeyword(kw, KeywordVersion::kVer13641995);
    auto in_default = LookupKeyword(kw);
    ASSERT_TRUE(in_default.has_value()) << kw;
    ASSERT_TRUE(in_1995.has_value()) << kw;
    if (!in_default.has_value() || !in_1995.has_value()) continue;
    EXPECT_EQ(*in_1995, *in_default) << kw;
    EXPECT_NE(*in_1995, TokenKind::kIdentifier) << kw;
  }
}

TEST(Lexer, WordsOutsideVerilog1995ListAreNotReserved) {
  for (const char* kw : kWordsAddedAfterVerilog1995) {
    EXPECT_FALSE(LookupKeyword(kw, KeywordVersion::kVer13641995).has_value())
        << kw << " is not listed in Table 22-1";
    EXPECT_TRUE(LookupKeyword(kw).has_value())
        << kw << " should still be reserved under the default list";
  }
}

TEST(Lexer, OrdinaryIdentifierIsReservedByNoList) {
  auto kw = LookupKeyword("my_signal", KeywordVersion::kVer13641995);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, WordsResemblingListedKeywordsAreNotReserved) {
  const char* const kNearMisses[] = {
      "REG",     "Reg",   "WIRE",   "Wire",     "MODULE",
      "regfile", "wired", "my_reg", "module_a", "endcase_",
  };
  for (const char* word : kNearMisses) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13641995).has_value())
        << word << " is not one of Table 22-1's spellings";
    EXPECT_FALSE(LookupKeyword(word).has_value())
        << word << " is not reserved under the default list either";
  }
}

}  // namespace
