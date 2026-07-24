#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// Table 22-2 with the keyword each entry stands for. The token kind is what
// makes this the inclusion claim rather than a weaker "something other than an
// identifier": a word carried over has to carry its meaning over with it.
struct VersionedWord {
  const char* text;
  TokenKind kind;
};

constexpr VersionedWord kTable222[] = {
    {"automatic", TokenKind::kKwAutomatic},
    {"cell", TokenKind::kKwCell},
    {"config", TokenKind::kKwConfig},
    {"design", TokenKind::kKwDesign},
    {"endconfig", TokenKind::kKwEndconfig},
    {"endgenerate", TokenKind::kKwEndgenerate},
    {"generate", TokenKind::kKwGenerate},
    {"genvar", TokenKind::kKwGenvar},
    {"incdir", TokenKind::kKwIncdir},
    {"include", TokenKind::kKwInclude},
    {"instance", TokenKind::kKwInstance},
    {"liblist", TokenKind::kKwLiblist},
    {"library", TokenKind::kKwLibrary},
    {"localparam", TokenKind::kKwLocalparam},
    {"noshowcancelled", TokenKind::kKwNoshowcancelled},
    {"pulsestyle_ondetect", TokenKind::kKwPulsestyleOndetect},
    {"pulsestyle_onevent", TokenKind::kKwPulsestyleOnevent},
    {"showcancelled", TokenKind::kKwShowcancelled},
    {"signed", TokenKind::kKwSigned},
    {"unsigned", TokenKind::kKwUnsigned},
    {"use", TokenKind::kKwUse},
};

// Table 22-1, the other list this version includes.
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

// Runs one word through a real `begin_keywords region for `version and reports
// the kind it lexes with. Going through the directive rather than calling the
// keyword table straight is the point: it is the region the directive opens
// that puts the version's list in force for the source that follows.
TokenKind KindInRegion(const std::string& version, const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"" + version + "\"\n" + word + "\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << version << " / " << word;

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  ADD_FAILURE() << word << " never reached the token stream";
  return TokenKind::kError;
}

// The same, for a specifier string that may not name any version at all. The
// diagnostics are read but not asserted on -- whether an unrecognized string is
// an error is settled elsewhere; what matters here is only which reserved word
// list the source that follows ends up being read under.
TokenKind KindAfterSpecifier(const std::string& spec, const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"" + spec + "\"\n" + word + "\n`end_keywords\n", f);

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  ADD_FAILURE() << word << " never reached the token stream";
  return TokenKind::kError;
}

// The directive carrying this version_specifier to the stage that applies it.
// The list is selected by name in the source and travels to the lexer as the
// marker the preprocessor emits, so the byte written has to be this version's
// and not the one belonging to the version it extends.
TEST(KeywordVersionPreprocessing, Verilog2005DirectiveEmitsItsOwnMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2005\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642005);

  PreprocFixture extended;
  auto other = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "x\n"
      "`end_keywords\n",
      extended);
  auto other_pos = other.find(kKeywordMarker);
  ASSERT_NE(other_pos, std::string::npos);
  EXPECT_NE(out[pos + 1], other[other_pos + 1]);
}

// The negative for the specifier, driven from real source rather than from a
// direct call on the string. Only the exact spelling names this list, so a word
// differing from it by its year or by a separator selects nothing and leaves
// the source that follows to be read under whatever list was already in force.
// `logic` is what makes that visible: this version leaves it an ordinary
// identifier while the default list reserves it, so the kind it lexes with says
// which of the two governed the region.
TEST(KeywordVersionPreprocessing, Verilog2005OnlyTheExactSpecifierSelectsIt) {
  // The spelling this subclause defines: the word is free.
  EXPECT_EQ(KindAfterSpecifier("1364-2005", "logic"), TokenKind::kIdentifier);

  const char* kNearMisses[] = {
      "1364-2004", "1364-2006", "1364_2005", "13642005", "1364-05",
  };
  for (const char* spec : kNearMisses) {
    EXPECT_EQ(KindAfterSpecifier(spec, "logic"), TokenKind::kKwLogic)
        << spec << " names no version, so this list was never put in force";
  }
}

// Table 22-1 carried through a real region, swept whole. Each word arrives at
// the lexer holding the keyword it holds under the list it comes from, which is
// what "includes the identifiers listed in 1364-1995" amounts to once the
// directive is in force.
TEST(KeywordVersionPreprocessing, Verilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto here = KindInRegion("1364-2005", word);
    EXPECT_NE(here, TokenKind::kIdentifier) << word << " is a reserved word";
    EXPECT_EQ(here, KindInRegion("1364-1995", word))
        << word << " keeps its meaning from the list it comes from";
  }
}

// Table 22-2 the same way, and with the keyword named outright. The paired leg
// under "1364-1995" is what makes each of these an inclusion: under the list
// that version reserves the very same word is an ordinary identifier, so its
// being a keyword here comes from the second list this version names.
TEST(KeywordVersionPreprocessing, Verilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const auto& word : kTable222) {
    EXPECT_EQ(KindInRegion("1364-2005", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-1995", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of the later of the two lists";
  }
}

// Table 22-3: the word this version contributes itself. Both lists it includes
// leave it an identifier, so the region opened for this version_specifier is
// the only one of the three under which it lexes as a keyword.
TEST(KeywordVersionPreprocessing, Verilog2005ReservesTheWordItAddsItself) {
  EXPECT_EQ(KindInRegion("1364-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2001", "uwire"), TokenKind::kIdentifier);
  EXPECT_EQ(KindInRegion("1364-1995", "uwire"), TokenKind::kIdentifier);
}

// The negative the three tables imply: a word none of them lists reaches the
// lexer as an ordinary identifier under this version, however firmly a later
// standard reserves it.
TEST(KeywordVersionPreprocessing, Verilog2005LeavesLaterWordsAsIdentifiers) {
  const char* kLater[] = {
      "logic",   "interface", "endinterface", "bit",     "byte",
      "int",     "longint",   "always_comb",  "package", "class",
      "typedef", "enum",      "string",       "nettype", "checker",
  };
  for (const char* word : kLater) {
    EXPECT_EQ(KindInRegion("1364-2005", word), TokenKind::kIdentifier)
        << word << " is outside the three tables this version names";
  }
}

}  // namespace
