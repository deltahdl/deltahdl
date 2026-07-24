#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// Table 22-2: the identifiers the "1364-2001" version_specifier adds on top of
// the list named by "1364-1995", transcribed in the order the table prints them
// (down each of its three columns).
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

// Table 22-1, which "1364-2001" carries over wholesale. It is half of what the
// specifier names, so the reserved set has to contain all of it as well as the
// additions above.
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

// Every word this implementation reserves that lies outside Table 22-1 and
// Table 22-2 together. Each entered the language in a standard later than
// IEEE Std 1364-2001, so naming that version has to leave every one of them an
// ordinary identifier. This is the exclusivity side of the rule, swept rather
// than sampled: the two tables name the whole reserved set, not a floor on it.
constexpr const char* kNotIn2001[] = {
    "uwire",
    "alias",
    "always_comb",
    "always_ff",
    "always_latch",
    "assert",
    "assume",
    "before",
    "bind",
    "bins",
    "binsof",
    "bit",
    "break",
    "byte",
    "chandle",
    "class",
    "clocking",
    "const",
    "constraint",
    "context",
    "continue",
    "cover",
    "covergroup",
    "coverpoint",
    "cross",
    "dist",
    "do",
    "endclass",
    "endclocking",
    "endgroup",
    "endinterface",
    "endpackage",
    "endprogram",
    "endproperty",
    "endsequence",
    "enum",
    "expect",
    "export",
    "extends",
    "extern",
    "final",
    "first_match",
    "foreach",
    "forkjoin",
    "iff",
    "ignore_bins",
    "illegal_bins",
    "import",
    "inside",
    "int",
    "interface",
    "intersect",
    "join_any",
    "join_none",
    "local",
    "logic",
    "longint",
    "matches",
    "modport",
    "new",
    "null",
    "package",
    "packed",
    "priority",
    "program",
    "property",
    "protected",
    "pure",
    "rand",
    "randc",
    "randcase",
    "randsequence",
    "ref",
    "return",
    "sequence",
    "shortint",
    "shortreal",
    "solve",
    "static",
    "string",
    "struct",
    "super",
    "tagged",
    "this",
    "throughout",
    "timeprecision",
    "timeunit",
    "type",
    "typedef",
    "union",
    "unique",
    "var",
    "virtual",
    "void",
    "wait_order",
    "wildcard",
    "with",
    "within",
    "accept_on",
    "checker",
    "endchecker",
    "eventually",
    "global",
    "implies",
    "let",
    "nexttime",
    "reject_on",
    "restrict",
    "s_always",
    "s_eventually",
    "s_nexttime",
    "s_until",
    "s_until_with",
    "strong",
    "sync_accept_on",
    "sync_reject_on",
    "unique0",
    "until",
    "until_with",
    "untyped",
    "weak",
    "implements",
    "interconnect",
    "nettype",
    "soft",
};

// The mapping itself, at the stage that owns it: this exact spelling is what
// names the 1364-2001 reserved word list, and nothing near it does. The
// rejected spellings matter as much as the accepted one -- a near miss that
// quietly resolved to this version would make the specifier a prefix match
// rather than a name.
TEST(Lexer, OnlyTheExactSpecifierNamesTheVerilog2001List) {
  auto version = ParseKeywordVersion("1364-2001");
  ASSERT_TRUE(version.has_value());
  EXPECT_EQ(*version, KeywordVersion::kVer13642001);

  const char* kNearMisses[] = {"1364-01",    "2001",      "1364-2001 ",
                               " 1364-2001", "1364_2001", "1364-2002",
                               "1364-20001", "1364200",   ""};
  for (const char* spec : kNearMisses) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << '"' << spec << "\" does not name this version";
  }
}

// The additions Table 22-2 lists are reserved words when "1364-2001" is the
// list in force, and each is the same reserved word it is under the
// implementation's default list -- the version list picks which words are
// reserved, not what a reserved word means. The second half of each case is
// what makes them *additional*: none of them is reserved under the list
// "1364-2001" builds on, so each one really is a word this version brings in
// rather than one it inherits.
TEST(Lexer, Verilog2001AdditionsYieldTheirOwnToken) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const char* kw : kTable222) {
    auto in_2001 = LookupKeyword(kw, KeywordVersion::kVer13642001);
    auto in_default = LookupKeyword(kw);
    ASSERT_TRUE(in_default.has_value()) << kw;
    ASSERT_TRUE(in_2001.has_value()) << kw << " is listed in Table 22-2";
    EXPECT_EQ(*in_2001, *in_default) << kw;
    EXPECT_NE(*in_2001, TokenKind::kIdentifier) << kw;
    EXPECT_FALSE(LookupKeyword(kw, KeywordVersion::kVer13641995).has_value())
        << kw << " is an addition, so the 1364-1995 list must not have it";
  }
}

// The inclusion half of the rule: this version takes in everything the
// "1364-1995" list names, so all 102 of Table 22-1's words stay reserved here,
// each still yielding its own token.
TEST(Lexer, Verilog2001IncludesTheWholeVerilog1995List) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* kw : kTable221) {
    auto in_2001 = LookupKeyword(kw, KeywordVersion::kVer13642001);
    auto in_default = LookupKeyword(kw);
    ASSERT_TRUE(in_default.has_value()) << kw;
    ASSERT_TRUE(in_2001.has_value()) << kw << " is carried over from 1364-1995";
    EXPECT_EQ(*in_2001, *in_default) << kw;
    EXPECT_NE(*in_2001, TokenKind::kIdentifier) << kw;
  }
}

// Exclusivity, swept over every reserved word this implementation knows that
// neither table lists. The second half of each case keeps the first honest: the
// word really is reserved somewhere, so its absence here is this list's doing
// rather than a word missing from the keyword table altogether. The sweep leads
// with `uwire` because it is the narrowest margin the rule has: the single word
// the very next version adds, and so the closest reserved word to this list
// without being in it.
TEST(Lexer, WordsOutsideTheVerilog2001ListAreNotReserved) {
  for (const char* kw : kNotIn2001) {
    EXPECT_FALSE(LookupKeyword(kw, KeywordVersion::kVer13642001).has_value())
        << kw << " is listed in neither Table 22-1 nor Table 22-2";
    EXPECT_TRUE(LookupKeyword(kw).has_value())
        << kw << " should still be reserved under the default list";
  }
}

// A word no standard has ever reserved is not reserved here either -- naming a
// version narrows the reserved set, it never widens it.
TEST(Lexer, OrdinaryIdentifierIsReservedByNoVerilog2001List) {
  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer13642001).has_value());
  EXPECT_FALSE(LookupKeyword("my_signal").has_value());
}

// The tables name exact spellings, so a word that differs from a listed one
// only in case, or that merely contains or extends one, falls outside them.
// These are the inputs a membership check built on prefixes or on
// case-insensitive matching would wrongly accept.
TEST(Lexer, WordsResemblingVerilog2001AdditionsAreNotReserved) {
  const char* kNearMisses[] = {
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
