#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// Table 22-1, the first of the five lists this version_specifier includes.
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

// Table 22-2, the additions "1364-2001" makes.
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

// The ten of Table 22-2 that the configuration-free neighbour of "1364-2001"
// leaves out. Two lists were published for that standard, and these ten are the
// only entries they disagree on, so they settle which of the two this version
// inherits: reserved here, dropped there.
constexpr const char* kConfigurationWords[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

// Table 22-3, the single addition "1364-2005" makes.
constexpr const char* kTable223[] = {
    "uwire",
};

// Table 22-4, the additions "1800-2005" makes -- the SystemVerilog vocabulary
// this version inherits whole.
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

// Table 22-5, the additions "1800-2009" makes -- mostly temporal-property
// vocabulary, alongside the checker construct, the let declaration, the
// restriction statement, the untyped formal, and the permissive case qualifier.
constexpr const char* kTable225[] = {
    "accept_on",      "checker",        "endchecker",   "eventually",
    "global",         "implies",        "let",          "nexttime",
    "reject_on",      "restrict",       "s_always",     "s_eventually",
    "s_nexttime",     "s_until",        "s_until_with", "strong",
    "sync_accept_on", "sync_reject_on", "unique0",      "until",
    "until_with",     "untyped",        "weak",
};

// Table 22-6: what this version_specifier contributes over and above the five
// lists it includes. Four words, and each opens a construct of its own -- the
// interface-class inheritance clause, the generic connection net, the
// user-defined nettype declaration, and the discardable qualifier a union type
// and a constraint expression both take.
constexpr const char* kTable226[] = {
    "implements",
    "interconnect",
    "nettype",
    "soft",
};

// The spelling of the version_specifier is what selects this list, so the
// string has to resolve to its own version and to nothing else. Its two nearest
// neighbours are the SystemVerilog standards on either side of it, each
// differing from it only in the year.
TEST(SystemVerilog2012KeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1800-2012");
  ASSERT_TRUE(parsed.has_value());
  EXPECT_EQ(*parsed, KeywordVersion::kVer18002012);

  auto previous = ParseKeywordVersion("1800-2009");
  ASSERT_TRUE(previous.has_value());
  EXPECT_NE(*parsed, *previous);

  auto next_standard = ParseKeywordVersion("1800-2017");
  ASSERT_TRUE(next_standard.has_value());
  EXPECT_NE(*parsed, *next_standard);
}

// The negative for that spelling. A version_specifier is a fixed string, so a
// word differing from it by a separator, by surrounding space, or by its year
// or standard number is not this one and names no list at all.
TEST(SystemVerilog2012KeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* kNotThisSpecifier[] = {
      "1800-2012 ", " 1800-2012", "1800_2012", "18002012", "1800-2013",
      "1800-2011",  "1800-12",    "1364-2012", "2012",     "1800-2012-noconfig",
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
TEST(SystemVerilog2012KeywordList, IncludesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto under_1995 = LookupKeyword(word, KeywordVersion::kVer13641995);
    ASSERT_TRUE(under_1995.has_value())
        << word << " is one of the words the included list reserves";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_1995)
        << word << " keeps the same keyword meaning here";
  }
}

// The second included list, swept the same way. "All previous versions"
// includes two lists published for the same standard -- one with the
// configuration words and one without -- and this test settles which of them
// governs: all twenty-one entries are reserved here, and the ten the
// configuration-free list drops are called out on their own, since they are the
// only entries on which the two disagree.
TEST(SystemVerilog2012KeywordList, IncludesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const char* word : kTable222) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    ASSERT_TRUE(under_2001.has_value())
        << word << " is one of the words the included list adds";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_2001)
        << word << " keeps the same keyword meaning here";
  }

  EXPECT_EQ(std::size(kConfigurationWords), 10u);
  for (const char* word : kConfigurationWords) {
    EXPECT_TRUE(LookupKeyword(word, KeywordVersion::kVer18002012).has_value())
        << word << " is reserved here";
    EXPECT_FALSE(
        LookupKeyword(word, KeywordVersion::kVer13642001Noconfig).has_value())
        << word << " is exactly what the configuration-free list leaves out";
  }
}

// The third included list, which holds one word. It is reserved here with the
// meaning it has under the list it comes from, and it is not reserved by either
// of the two lists that one is itself built on -- so its being a keyword here
// can only have come from the third inclusion.
TEST(SystemVerilog2012KeywordList, IncludesTheVerilog2005Keyword) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* word = kTable223[0];

  auto under_2005 = LookupKeyword(word, KeywordVersion::kVer13642005);
  ASSERT_TRUE(under_2005.has_value());

  auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
  ASSERT_TRUE(here.has_value());
  EXPECT_EQ(*here, *under_2005);
  EXPECT_EQ(*here, TokenKind::kKwUwire);

  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642001).has_value());
}

// The fourth included list, swept whole. Its entries are reserved here with the
// meaning they carry under the list they come from, and each is an ordinary
// identifier under "1364-2005" -- the union of the three lists that one is
// itself built on -- so their being keywords here traces to the fourth
// inclusion and to nothing earlier.
TEST(SystemVerilog2012KeywordList, IncludesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kTable224), 97u);
  for (const char* word : kTable224) {
    auto under_sv2005 = LookupKeyword(word, KeywordVersion::kVer18002005);
    ASSERT_TRUE(under_sv2005.has_value())
        << word << " is one of the words the included list adds";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_sv2005)
        << word << " keeps the same keyword meaning here";

    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642005).has_value())
        << word << " is not reserved by anything that list is built on";
  }
}

// The fifth included list, and the last one before this version's own. Its
// entries are reserved here with the meaning they carry under the list they
// come from, and each is an ordinary identifier under "1800-2005" -- the union
// of the four lists that one is itself built on -- so their being keywords here
// traces to the fifth inclusion.
TEST(SystemVerilog2012KeywordList, IncludesEverySystemVerilog2009Keyword) {
  EXPECT_EQ(std::size(kTable225), 23u);
  for (const char* word : kTable225) {
    auto under_sv2009 = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(under_sv2009.has_value())
        << word << " is one of the words the included list adds";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_sv2009)
        << word << " keeps the same keyword meaning here";

    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002005).has_value())
        << word << " is not reserved by anything that list is built on";
  }
}

// Table 22-6 and what makes its entries *additions* rather than inheritances:
// each is reserved here and is an ordinary identifier under the last of the
// five lists this version includes, which is the union of all five. The sweep
// over those five lists is the other half of the claim -- across every word
// they hold, being reserved here but not under "1800-2009" happens for none of
// them, so Table 22-6 accounts for the whole difference between the two lists.
TEST(SystemVerilog2012KeywordList,
     AddedWordsAreTheWholeDifferenceFromIncludedLists) {
  EXPECT_EQ(std::size(kTable226), 4u);

  struct AddedWord {
    const char* text;
    TokenKind kind;
  };
  const AddedWord kAdded[] = {
      {"implements", TokenKind::kKwImplements},
      {"interconnect", TokenKind::kKwInterconnect},
      {"nettype", TokenKind::kKwNettype},
      {"soft", TokenKind::kKwSoft},
  };
  for (const auto& word : kAdded) {
    auto here = LookupKeyword(word.text, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value())
        << word.text << " is one of the words this version adds";
    // Naming the keyword outright is what makes this an addition claim rather
    // than the weaker "something other than an identifier".
    EXPECT_EQ(*here, word.kind) << word.text;
    EXPECT_FALSE(
        LookupKeyword(word.text, KeywordVersion::kVer18002009).has_value())
        << word.text << " is not reserved by the last of the included lists";
  }

  size_t newly_reserved = 0;
  auto count_new = [&newly_reserved](const char* word) {
    if (!LookupKeyword(word, KeywordVersion::kVer18002009).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer18002012).has_value()) {
      ++newly_reserved;
    }
  };
  for (const char* word : kTable221) count_new(word);
  for (const char* word : kTable222) count_new(word);
  for (const char* word : kTable223) count_new(word);
  for (const char* word : kTable224) count_new(word);
  for (const char* word : kTable225) count_new(word);
  EXPECT_EQ(newly_reserved, 0u)
      << "the included lists contribute nothing this version reserves anew";
}

// The six tables put together are the list, so their sizes add up to it and
// none of them repeats a word another already holds. Without this the sweeps
// above could each pass while between them covering only part of the list.
TEST(SystemVerilog2012KeywordList, TheListIsTheSixTablesTogether) {
  EXPECT_EQ(std::size(kTable221) + std::size(kTable222) + std::size(kTable223) +
                std::size(kTable224) + std::size(kTable225) +
                std::size(kTable226),
            248u);

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
    for (const char* w : kTable225) {
      if (word == w) ++seen;
    }
    for (const char* w : kTable226) {
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
  for (const char* word : kTable225) {
    EXPECT_EQ(count_across_tables(word), 1u) << word << " is counted twice";
  }
  for (const char* word : kTable226) {
    EXPECT_EQ(count_across_tables(word), 1u) << word << " is counted twice";
  }
}

// The list bounds what is reserved from above as well as from below: naming
// five included tables plus one of its own says nothing outside them is a
// reserved word here.
//
// Every earlier version in this ladder can be bounded from above by pointing at
// the words the *next* one introduces. This version cannot -- it is the last
// one that introduces any -- so what is checked instead is that words shaped
// like its own additions, and like the additions of the lists it includes, are
// not on it. Each near-miss below differs from a real entry by a prefix, a
// suffix, or a separator, which is exactly what a table membership test that
// matched loosely would let through; that the entries themselves are reserved
// is what the sweeps above establish.
TEST(SystemVerilog2012KeywordList, WordsOutsideTheSixTablesAreNotReserved) {
  const char* kNotWords[] = {
      "implement",     "implemented",    "implements_",   "interconnects",
      "inter_connect", "interconnected", "nettypes",      "net_type",
      "nettype_",      "softly",         "soft_",         "softer",
      "s_soft",        "endnettype",     "endimplements",
  };
  for (const char* word : kNotWords) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002012).has_value())
        << word << " is not one of the identifiers the six tables list";
  }
}

}  // namespace
