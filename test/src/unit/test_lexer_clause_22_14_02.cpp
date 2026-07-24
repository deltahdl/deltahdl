#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// Table 22-1: the reserved word list the "1364-1995" version_specifier names,
// transcribed in the order the table prints it (down each of its three
// columns). Nothing outside this list is reserved under that specifier.
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

// Every word this implementation reserves that Table 22-1 does not list. Each
// one entered the language in a standard later than IEEE Std 1364-1995, so
// under the "1364-1995" specifier each is an ordinary identifier. They are the
// exclusivity side of the rule: naming that version must free all of them, not
// just the few the LRM's examples happen to mention.
constexpr const char* kNotInTable221[] = {
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

// Membership: each of Table 22-1's identifiers is a reserved word when the
// "1364-1995" list is the one in force. Membership is also all the version
// list decides — a word the table lists is the same reserved word under this
// list as under the implementation's default, down to the token it produces.
// Comparing against the default list rather than against a hand-written
// expectation keeps the check exhaustive while still pinning each word to one
// specific token rather than merely to "reserved".
TEST(Lexer, Verilog1995KeywordsYieldTheirOwnToken) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* kw : kTable221) {
    auto in_1995 = LookupKeyword(kw, KeywordVersion::kVer13641995);
    auto in_default = LookupKeyword(kw);
    ASSERT_TRUE(in_default.has_value()) << kw;
    ASSERT_TRUE(in_1995.has_value()) << kw;
    EXPECT_EQ(*in_1995, *in_default) << kw;
    EXPECT_NE(*in_1995, TokenKind::kIdentifier) << kw;
  }
}

// Exclusivity, swept over every reserved word this implementation knows that
// Table 22-1 omits. The second half of each case is the witness that keeps the
// first half honest: the word really is reserved somewhere, so its absence
// under "1364-1995" is that list's doing rather than a word missing from the
// keyword table altogether.
TEST(Lexer, WordsOutsideVerilog1995ListAreNotReserved) {
  for (const char* kw : kNotInTable221) {
    EXPECT_FALSE(LookupKeyword(kw, KeywordVersion::kVer13641995).has_value())
        << kw << " is not listed in Table 22-1";
    EXPECT_TRUE(LookupKeyword(kw).has_value())
        << kw << " should still be reserved under the default list";
  }
}

// A word that no standard has ever reserved is not reserved here either — the
// version list narrows the reserved set, it does not widen it.
TEST(Lexer, OrdinaryIdentifierIsReservedByNoList) {
  auto kw = LookupKeyword("my_signal", KeywordVersion::kVer13641995);
  EXPECT_FALSE(kw.has_value());
}

// Exclusivity at its narrowest margin: the list names exact spellings, so a
// word that differs from a listed one only in case, or that merely contains
// one, falls outside it. These are the inputs a membership test built on
// prefixes or case-insensitive matching would wrongly accept.
TEST(Lexer, WordsResemblingListedKeywordsAreNotReserved) {
  const char* kNearMisses[] = {
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
