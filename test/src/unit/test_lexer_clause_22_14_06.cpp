#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// Table 22-1, the list "1364-1995" reserves and the first of the three this
// version_specifier names as included.
constexpr const char* kTable221[] = {
    "always",    "and",          "assign",     "begin",     "buf",
    "bufif0",    "bufif1",       "case",       "casex",     "casez",
    "cmos",      "deassign",     "default",    "defparam",  "disable",
    "edge",      "else",         "end",        "endcase",   "endfunction",
    "endmodule", "endprimitive", "endspecify", "endtable",  "endtask",
    "event",     "for",          "force",      "forever",   "fork",
    "function",  "highz0",       "highz1",     "if",        "ifnone",
    "initial",   "inout",        "input",      "integer",   "join",
    "large",     "macromodule",  "medium",     "module",    "nand",
    "negedge",   "nmos",         "nor",        "not",       "notif0",
    "notif1",    "or",           "output",     "parameter", "pmos",
    "posedge",   "primitive",    "pull0",      "pull1",     "pulldown",
    "pullup",    "rcmos",        "real",       "realtime",  "reg",
    "release",   "repeat",       "rnmos",      "rpmos",     "rtran",
    "rtranif0",  "rtranif1",     "scalared",   "small",     "specify",
    "specparam", "strong0",      "strong1",    "supply0",   "supply1",
    "table",     "task",         "time",       "tran",      "tranif0",
    "tranif1",   "tri",          "tri0",       "tri1",      "triand",
    "trior",     "trireg",       "vectored",   "wait",      "wand",
    "weak0",     "weak1",        "while",      "wire",      "wor",
    "xnor",      "xor",
};

// Table 22-2, the additions "1364-2001" makes. Named whole here -- the ten
// configuration words among them.
constexpr const char* kTable222[] = {
    "automatic",
    "cell",
    "config",
    "design",
    "endconfig",
    "endgenerate",
    "generate",
    "genvar",
    "incdir",
    "include",
    "instance",
    "liblist",
    "library",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
    "use",
};

// Table 22-3, the single addition "1364-2005" makes and the third of the lists
// this version includes.
constexpr const char* kTable223[] = {
    "uwire",
};

// Table 22-4: what this version contributes over and above the three lists it
// includes. This is the list that carries the SystemVerilog vocabulary -- the
// integer and aggregate types, the class and interface machinery, the assertion
// vocabulary, and the procedural statements Verilog did not have.
constexpr const char* kTable224[] = {
    "alias",         "always_comb",  "always_ff",    "always_latch",
    "assert",        "assume",       "before",       "bind",
    "bins",          "binsof",       "bit",          "break",
    "byte",          "chandle",      "class",        "clocking",
    "const",         "constraint",   "context",      "continue",
    "cover",         "covergroup",   "coverpoint",   "cross",
    "dist",          "do",           "endclass",     "endclocking",
    "endgroup",      "endinterface", "endpackage",   "endprogram",
    "endproperty",   "endsequence",  "enum",         "expect",
    "export",        "extends",      "extern",       "final",
    "first_match",   "foreach",      "forkjoin",     "iff",
    "ignore_bins",   "illegal_bins", "import",       "inside",
    "int",           "interface",    "intersect",    "join_any",
    "join_none",     "local",        "logic",        "longint",
    "matches",       "modport",      "new",          "null",
    "package",       "packed",       "priority",     "program",
    "property",      "protected",    "pure",         "rand",
    "randc",         "randcase",     "randsequence", "ref",
    "return",        "sequence",     "shortint",     "shortreal",
    "solve",         "static",       "string",       "struct",
    "super",         "tagged",       "this",         "throughout",
    "timeprecision", "timeunit",     "type",         "typedef",
    "union",         "unique",       "var",          "virtual",
    "void",          "wait_order",   "wildcard",     "with",
    "within",
};

// The spelling of the version_specifier is what selects this list, so the
// string has to resolve to its own version and to nothing else. Its two nearest
// neighbours are the Verilog standard published the same year, whose specifier
// differs only in its leading number, and the next SystemVerilog standard,
// whose specifier differs only in its year.
TEST(SystemVerilog2005KeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1800-2005");
  ASSERT_TRUE(parsed.has_value());
  EXPECT_EQ(*parsed, KeywordVersion::kVer18002005);

  auto same_year = ParseKeywordVersion("1364-2005");
  ASSERT_TRUE(same_year.has_value());
  EXPECT_NE(*parsed, *same_year);

  auto next_standard = ParseKeywordVersion("1800-2009");
  ASSERT_TRUE(next_standard.has_value());
  EXPECT_NE(*parsed, *next_standard);
}

// The negative for that spelling. A version_specifier is a fixed string, so a
// word differing from it by a separator, by surrounding space, or by its year
// or standard number is not this one and names no list at all.
TEST(SystemVerilog2005KeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* kNotThisSpecifier[] = {
      "1800-2005 ", " 1800-2005", "1800_2005", "18002005", "1800-2006",
      "1800-2004",  "1800-05",    "2005",      "1800",     "1800-2005-noconfig",
  };
  for (const char* spec : kNotThisSpecifier) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << spec << " is not the spelling this subclause defines";
  }
}

// The first included list, swept whole rather than sampled. Each word is read
// under both versions from the same lookup, so "1364-1995" is the baseline the
// inclusion is measured against instead of an assumption, and the keyword each
// word resolves to has to be the same one -- being reserved for a different
// meaning would not be inclusion.
TEST(SystemVerilog2005KeywordList, IncludesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto under_1995 = LookupKeyword(word, KeywordVersion::kVer13641995);
    ASSERT_TRUE(under_1995.has_value())
        << word << " is one of the words the included list reserves";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002005);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_1995)
        << word << " keeps the same keyword meaning here";
  }
}

// The second included list, swept the same way and included entire: the ten
// configuration words that one neighbouring version_specifier drops are
// reserved here along with the other eleven.
TEST(SystemVerilog2005KeywordList, IncludesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const char* word : kTable222) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    ASSERT_TRUE(under_2001.has_value())
        << word << " is one of the words the included list adds";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002005);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_2001)
        << word << " keeps the same keyword meaning here";
  }
}

// The third included list, which holds one word. It is reserved here with the
// meaning it has under the list it comes from, and it is not reserved by either
// of the two lists that one is itself built on -- so its being a keyword here
// can only have come from the third inclusion.
TEST(SystemVerilog2005KeywordList, IncludesTheVerilog2005Keyword) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* word = kTable223[0];

  auto under_2005 = LookupKeyword(word, KeywordVersion::kVer13642005);
  ASSERT_TRUE(under_2005.has_value());

  auto here = LookupKeyword(word, KeywordVersion::kVer18002005);
  ASSERT_TRUE(here.has_value());
  EXPECT_EQ(*here, *under_2005);
  EXPECT_EQ(*here, TokenKind::kKwUwire);

  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642001).has_value());
}

// Table 22-4 and what makes its entries *additions* rather than inheritances:
// each is reserved here and is an ordinary identifier under the last of the
// three lists this version includes, which is the union of all three. The sweep
// over those three lists is the other half of the claim -- across every word
// they hold, being reserved here but not under "1364-2005" happens for none of
// them, so Table 22-4 accounts for the whole difference between the two lists.
TEST(SystemVerilog2005KeywordList,
     AddedWordsAreTheWholeDifferenceFromIncludedLists) {
  EXPECT_EQ(std::size(kTable224), 97u);
  for (const char* word : kTable224) {
    EXPECT_TRUE(LookupKeyword(word, KeywordVersion::kVer18002005).has_value())
        << word << " is one of the words this version adds";
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642005).has_value())
        << word << " is not reserved by the last of the included lists";
  }

  size_t newly_reserved = 0;
  for (const char* word : kTable221) {
    if (!LookupKeyword(word, KeywordVersion::kVer13642005).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer18002005).has_value()) {
      ++newly_reserved;
    }
  }
  for (const char* word : kTable222) {
    if (!LookupKeyword(word, KeywordVersion::kVer13642005).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer18002005).has_value()) {
      ++newly_reserved;
    }
  }
  for (const char* word : kTable223) {
    if (!LookupKeyword(word, KeywordVersion::kVer13642005).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer18002005).has_value()) {
      ++newly_reserved;
    }
  }
  EXPECT_EQ(newly_reserved, 0u)
      << "the included lists contribute nothing this version reserves anew";
}

// The four tables put together are the list, so their sizes add up to it and
// none of them repeats a word another already holds. Without this the sweeps
// above could each pass while between them covering only part of the list.
TEST(SystemVerilog2005KeywordList, TheListIsTheFourTablesTogether) {
  EXPECT_EQ(std::size(kTable221) + std::size(kTable222) + std::size(kTable223) +
                std::size(kTable224),
            221u);

  auto count_across_tables = [](const std::string& word) {
    size_t seen = 0;
    for (const char* w : kTable221) {
      if (word == w) ++seen;
    }
    for (const char* w : kTable222) {
      if (word == w) ++seen;
    }
    for (const char* w : kTable223) {
      if (word == w) ++seen;
    }
    for (const char* w : kTable224) {
      if (word == w) ++seen;
    }
    return seen;
  };
  for (const char* word : kTable221) {
    EXPECT_EQ(count_across_tables(word), 1u) << word << " is counted twice";
  }
  for (const char* word : kTable222) {
    EXPECT_EQ(count_across_tables(word), 1u) << word << " is counted twice";
  }
  for (const char* word : kTable223) {
    EXPECT_EQ(count_across_tables(word), 1u) << word << " is counted twice";
  }
  for (const char* word : kTable224) {
    EXPECT_EQ(count_across_tables(word), 1u) << word << " is counted twice";
  }
}

// The list bounds what is reserved from above as well as from below: naming
// three included tables plus one of its own says nothing outside them is a
// reserved word here. The words later standards introduce are what this matters
// for, and they stay unreserved under this version.
TEST(SystemVerilog2005KeywordList, WordsOutsideTheFourTablesAreNotReserved) {
  const char* kLater[] = {
      "accept_on", "checker", "endchecker", "eventually",     "global",
      "implies",   "let",     "nexttime",   "reject_on",      "restrict",
      "s_always",  "s_until", "strong",     "sync_accept_on", "unique0",
      "until",     "untyped", "weak",       "implements",     "interconnect",
      "nettype",   "soft",
  };
  for (const char* word : kLater) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002005).has_value())
        << word << " belongs to a list later than the four this one names";
  }
}

}  // namespace
