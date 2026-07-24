#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// Table 22-1, the reserved word list the "1364-1995" version_specifier names.
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

// A sample of the words later standards reserve that Table 22-1 omits, spread
// across the standards that introduced them: 1364-2001, 1364-2005, 1800-2005,
// 1800-2009, and 1800-2012. Under the "1364-1995" specifier every one of them
// is an ordinary identifier.
constexpr const char* kNotInTable221[] = {
    "automatic", "generate", "genvar",  "localparam", "signed", "unsigned",
    "uwire",     "logic",    "bit",     "int",        "byte",   "string",
    "interface", "class",    "package", "typedef",    "enum",   "always_comb",
    "checker",   "let",      "global",  "until",      "soft",   "nettype",
};

// Lexes `src` and returns the kind of the first token whose spelling is
// `word`, or kError when the token never appears.
TokenKind KindOfWordIn(const std::string& src, const std::string& word) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<preprocessed>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  return TokenKind::kError;
}

// Puts `word` inside a real `begin_keywords "1364-1995" region, runs the
// preprocessor over it, and reports the kind the lexer then gives the word.
// Nothing here hand-builds the version marker: the directive is written as
// source and the marker the preprocessor emits is what reaches the lexer.
TokenKind KindInsideRegion(const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-1995\"\n" + word + "\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << word;
  return KindOfWordIn(out, word);
}

// The same word with no directive governing it, so the implementation's
// default reserved word list decides its kind.
TokenKind KindUnderDefaultList(const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(word + "\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << word;
  return KindOfWordIn(out, word);
}

// The directive selects this list by handing the lexer a marker naming the
// version. This specifier is the one whose version byte is zero, so the byte
// the preprocessor writes is an embedded NUL — source following it has to keep
// lexing normally for the list to take effect at all, which is what the tokens
// checked at the end show.
TEST(KeywordVersionPreprocessing, Verilog1995DirectiveEmitsItsVersionMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-1995\"\n"
      "reg logic;\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  ASSERT_LT(pos + 1, out.size());
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13641995);
  EXPECT_EQ(out[pos + 1], '\0');

  EXPECT_EQ(KindOfWordIn(out, "reg"), TokenKind::kKwReg);
  EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kIdentifier);
}

// Membership carried through the real directive path: every word Table 22-1
// lists is still a reserved word inside the region, and is the very same
// reserved word it is under the default list — the list selects which words
// are reserved, not what a reserved word means.
TEST(KeywordVersionPreprocessing,
     EveryVerilog1995WordStaysReservedInTheRegion) {
  for (const char* word : kTable221) {
    auto in_region = KindInsideRegion(word);
    auto by_default = KindUnderDefaultList(word);
    EXPECT_NE(in_region, TokenKind::kIdentifier) << word;
    EXPECT_NE(in_region, TokenKind::kError) << word;
    EXPECT_EQ(in_region, by_default) << word;
  }
}

// The exclusivity side through the same path: a word a later standard reserved
// arrives inside the region as a plain identifier, while the same word under
// the default list arrives as a keyword.
TEST(KeywordVersionPreprocessing,
     WordsOutsideVerilog1995ListBecomeIdentifiers) {
  for (const char* word : kNotInTable221) {
    EXPECT_EQ(KindInsideRegion(word), TokenKind::kIdentifier) << word;
    EXPECT_NE(KindUnderDefaultList(word), TokenKind::kIdentifier) << word;
  }
}

// The negative form of the mapping: only this exact spelling names Table 22-1.
// A near miss is not a quiet fallback to the 1995 list — it is rejected, and
// no version marker is emitted, so the words the list would have freed stay
// reserved.
TEST(KeywordVersionPreprocessing,
     NearMissSpecifierDoesNotSelectVerilog1995List) {
  const char* kNearMisses[] = {"1364-95",    "1995",      "1364-1995 ",
                               " 1364-1995", "1364_1995", "1364-1996"};
  for (const char* spec : kNearMisses) {
    PreprocFixture f;
    auto out = Preprocess(std::string("`begin_keywords \"") + spec +
                              "\"\n"
                              "reg logic;\n"
                              "`end_keywords\n",
                          f);
    EXPECT_TRUE(f.diag.HasErrors()) << spec;
    EXPECT_EQ(out.find(kKeywordMarker), std::string::npos) << spec;
    EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kKwLogic) << spec;
  }
}

}  // namespace
