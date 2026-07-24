#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// Table 22-2: what "1364-2001" adds to the list it inherits.
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

// Table 22-1, which this version includes whole.
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

// A sample of the words later standards reserve that neither table lists,
// spread across the standards that introduced them: 1364-2005, 1800-2005,
// 1800-2009, and 1800-2012. Under this specifier every one is an ordinary
// identifier. `uwire` leads the list because it is the sole word the very next
// version adds, and so the closest one to this list without being in it.
constexpr const char* kNotIn2001[] = {
    "uwire",        "logic",      "bit",         "int",    "byte",
    "string",       "var",        "interface",   "class",  "package",
    "typedef",      "enum",       "always_comb", "assert", "checker",
    "let",          "global",     "until",       "soft",   "nettype",
    "interconnect", "implements",
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

// Puts `word` inside a real `begin_keywords region for `version`, runs the
// preprocessor over it, and reports the kind the lexer then gives the word.
// Nothing here hand-builds the version marker: the directive is written as
// source and the marker the preprocessor emits is what reaches the lexer.
TokenKind KindInRegion(const char* version, const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(std::string("`begin_keywords \"") + version + "\"\n" +
                            word + "\n`end_keywords\n",
                        f);
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
// version. The tokens checked at the end are what show the marker took effect:
// an addition of this version arrives reserved and a word from a later one
// arrives as a plain identifier.
TEST(KeywordVersionPreprocessing, Verilog2001DirectiveEmitsItsVersionMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "genvar logic;\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  ASSERT_LT(pos + 1, out.size());
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642001);

  EXPECT_EQ(KindOfWordIn(out, "genvar"), TokenKind::kKwGenvar);
  EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kIdentifier);
}

// Membership of the additions carried through the real directive path: every
// word Table 22-2 lists arrives inside the region as a reserved word, and as
// the same reserved word it is under the default list. The 1364-1995 leg is
// the *additional* part of the claim -- these words are absent from the list
// this version builds on, so each one is genuinely brought in here.
TEST(KeywordVersionPreprocessing, Verilog2001AdditionsAreReservedInTheRegion) {
  for (const char* word : kTable222) {
    auto in_region = KindInRegion("1364-2001", word);
    EXPECT_NE(in_region, TokenKind::kIdentifier) << word;
    EXPECT_NE(in_region, TokenKind::kError) << word;
    EXPECT_EQ(in_region, KindUnderDefaultList(word)) << word;
    EXPECT_EQ(KindInRegion("1364-1995", word), TokenKind::kIdentifier)
        << word << " is an addition of this version";
  }
}

// The inclusion half through the same path: all 102 words the earlier list
// names are still reserved inside a region governed by this one.
TEST(KeywordVersionPreprocessing,
     EveryVerilog1995WordStaysReservedUnderVerilog2001) {
  for (const char* word : kTable221) {
    auto in_region = KindInRegion("1364-2001", word);
    EXPECT_NE(in_region, TokenKind::kIdentifier) << word;
    EXPECT_NE(in_region, TokenKind::kError) << word;
    EXPECT_EQ(in_region, KindUnderDefaultList(word)) << word;
  }
}

// The exclusivity side through the same path: a word a later standard reserved
// arrives inside the region as a plain identifier, while the same word under
// the default list arrives as a keyword.
TEST(KeywordVersionPreprocessing,
     WordsOutsideVerilog2001ListBecomeIdentifiers) {
  for (const char* word : kNotIn2001) {
    EXPECT_EQ(KindInRegion("1364-2001", word), TokenKind::kIdentifier) << word;
    EXPECT_NE(KindUnderDefaultList(word), TokenKind::kIdentifier) << word;
  }
}

// The negative form of the mapping: only this exact spelling names the
// 1364-2001 list. A near miss is not a quiet fallback to it -- it is rejected,
// and no version marker is emitted at all, so the default list stays in force
// and a word this version would have left reserved is still reserved while a
// word it would have freed is still a keyword.
TEST(KeywordVersionPreprocessing, NearMissSpecifierDoesNotSelectThisList) {
  const char* kNearMisses[] = {"1364-01",    "2001",      "1364-2001 ",
                               " 1364-2001", "1364_2001", "1364-2002",
                               "1364-20001"};
  for (const char* spec : kNearMisses) {
    PreprocFixture f;
    auto out = Preprocess(std::string("`begin_keywords \"") + spec +
                              "\"\n"
                              "genvar logic;\n"
                              "`end_keywords\n",
                          f);
    EXPECT_TRUE(f.diag.HasErrors()) << spec;
    EXPECT_EQ(out.find(kKeywordMarker), std::string::npos) << spec;
    EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kKwLogic) << spec;
  }
}

}  // namespace
