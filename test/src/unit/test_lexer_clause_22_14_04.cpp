#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// The identifiers this version_specifier drops from the list "1364-2001"
// reserves. These ten are the whole of what distinguishes it from that
// version.
constexpr const char* kExcluded[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

// The remainder of Table 22-2 -- the additions of "1364-2001" that this
// version_specifier keeps reserved. Together with kExcluded this is the whole
// table, which is what makes the pair a partition rather than two samples.
constexpr const char* kKept[] = {
    "automatic",
    "endgenerate",
    "generate",
    "genvar",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
};

// Table 22-1, inherited whole by "1364-2001" and so by this version_specifier
// too: the exception this subclause names reaches only Table 22-2.
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

bool IsExcluded(const std::string& word) {
  for (const char* w : kExcluded) {
    if (word == w) return true;
  }
  return false;
}

// The spelling of the version_specifier itself is what selects this list, so
// the string has to resolve to its own version and not to anything else.
TEST(NoconfigKeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1364-2001-noconfig");
  ASSERT_TRUE(parsed.has_value());
  EXPECT_EQ(*parsed, KeywordVersion::kVer13642001Noconfig);

  // The version it is defined in terms of is a different one; if the two
  // collapsed onto the same value the exception below could not be observed
  // at all.
  auto plain = ParseKeywordVersion("1364-2001");
  ASSERT_TRUE(plain.has_value());
  EXPECT_NE(*parsed, *plain);
}

// The negative for that spelling. A version_specifier is a fixed string, so a
// word differing from it by case, by a missing separator, or by standing on
// its own is not this one and is not recognized at all.
TEST(NoconfigKeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* kNotThisSpecifier[] = {
      "1364-2001-NOCONFIG",  "1364-2001-Noconfig",
      "1364-2001noconfig",   "1364-2001 -noconfig",
      "1364-2001-noconfig ", " 1364-2001-noconfig",
      "1364-2001-no-config", "noconfig",
      "1364-2001-noconfigx",
  };
  for (const char* spec : kNotThisSpecifier) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << spec << " is not the spelling this subclause defines";
  }
}

// The subclause in the exact shape it is written: this version behaves as
// "1364-2001" does, except that ten identifiers drop off the list. Sweeping
// both tables and comparing the two versions word for word is what makes the
// claim -- rather than a sample of it -- the thing being checked. Every word
// either resolves to the same keyword under both, or is one of the ten and
// resolves under "1364-2001" alone.
TEST(NoconfigKeywordList, MatchesVerilog2001ExceptForTheExcludedTen) {
  size_t excluded_seen = 0;
  size_t kept_seen = 0;

  auto compare = [&](const char* word) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    auto under_noconfig =
        LookupKeyword(word, KeywordVersion::kVer13642001Noconfig);

    // Both legs are read from the same lookup, so the "1364-2001" side is the
    // baseline the exception is measured against rather than an assumption.
    ASSERT_TRUE(under_2001.has_value())
        << word << " is reserved by the version this one is defined from";

    if (IsExcluded(word)) {
      EXPECT_FALSE(under_noconfig.has_value())
          << word << " is one of the ten this version drops";
      ++excluded_seen;
    } else {
      ASSERT_TRUE(under_noconfig.has_value())
          << word << " is not among the ten and stays reserved";
      EXPECT_EQ(*under_noconfig, *under_2001)
          << word << " keeps the same keyword meaning under both versions";
      ++kept_seen;
    }
  };

  for (const char* word : kTable221) compare(word);
  for (const char* word : kExcluded) compare(word);
  for (const char* word : kKept) compare(word);

  EXPECT_EQ(excluded_seen, 10u);
  EXPECT_EQ(kept_seen, std::size(kTable221) + std::size(kKept));
}

// The two halves of Table 22-2 partition it: ten dropped and eleven kept makes
// the twenty-one entries "1364-2001" adds. Without this the sweep above could
// pass while silently covering only part of the table.
TEST(NoconfigKeywordList, SplitsVerilog2001AdditionsIntoTenAndEleven) {
  EXPECT_EQ(std::size(kExcluded), 10u);
  EXPECT_EQ(std::size(kKept), 11u);
  EXPECT_EQ(std::size(kExcluded) + std::size(kKept), 21u);
  EXPECT_EQ(std::size(kTable221), 102u);

  // The two groups are disjoint, so no word is counted on both sides.
  for (const char* word : kKept) {
    EXPECT_FALSE(IsExcluded(word)) << word;
  }
}

// The whole inherited list, not a sample of it: the exception this subclause
// names reaches Table 22-2 only, so every one of Table 22-1's entries has to
// survive into this version untouched.
TEST(NoconfigKeywordList, KeepsAllVerilog1995Keywords) {
  for (const char* kw : kTable221) {
    EXPECT_TRUE(
        LookupKeyword(kw, KeywordVersion::kVer13642001Noconfig).has_value())
        << kw << " is inherited from Table 22-1 and stays reserved";
  }
}

// Behaving as "1364-2001" does bounds the list from above as well as below:
// words later versions introduce are no more reserved here than they are
// there. `uwire` is the sharpest case, being the sole addition of the very
// next version.
TEST(NoconfigKeywordList, LaterVersionKeywordsAreNotRecognized) {
  const char* kLater[] = {
      "uwire",   "logic",       "interface", "bit",        "byte",
      "int",     "always_comb", "package",   "endpackage", "shortreal",
      "nettype", "soft",        "untyped",
  };
  for (const char* kw : kLater) {
    EXPECT_FALSE(
        LookupKeyword(kw, KeywordVersion::kVer13642001Noconfig).has_value())
        << kw << " belongs to a later list than this one";
  }
}

}  // namespace
