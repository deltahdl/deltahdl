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

// A word paired with the keyword it stands for. The token kind is what makes an
// assertion an inclusion or an addition claim rather than a weaker "something
// other than an identifier": a word this list reserves has to arrive at the
// lexer holding a particular meaning.
struct VersionedWord {
  const char* text;
  TokenKind kind;
};

// Table 22-5 -- what this version_specifier contributes over the four lists it
// includes, with the keyword each entry names.
constexpr VersionedWord kTable225[] = {
    {"accept_on", TokenKind::kKwAcceptOn},
    {"checker", TokenKind::kKwChecker},
    {"endchecker", TokenKind::kKwEndchecker},
    {"eventually", TokenKind::kKwEventually},
    {"global", TokenKind::kKwGlobal},
    {"implies", TokenKind::kKwImplies},
    {"let", TokenKind::kKwLet},
    {"nexttime", TokenKind::kKwNexttime},
    {"reject_on", TokenKind::kKwRejectOn},
    {"restrict", TokenKind::kKwRestrict},
    {"s_always", TokenKind::kKwSAlways},
    {"s_eventually", TokenKind::kKwSEventually},
    {"s_nexttime", TokenKind::kKwSNexttime},
    {"s_until", TokenKind::kKwSUntil},
    {"s_until_with", TokenKind::kKwSUntilWith},
    {"strong", TokenKind::kKwStrong},
    {"sync_accept_on", TokenKind::kKwSyncAcceptOn},
    {"sync_reject_on", TokenKind::kKwSyncRejectOn},
    {"unique0", TokenKind::kKwUnique0},
    {"until", TokenKind::kKwUntil},
    {"until_with", TokenKind::kKwUntilWith},
    {"untyped", TokenKind::kKwUntyped},
    {"weak", TokenKind::kKwWeak},
};

// Table 22-4, the fourth of the four included lists, with its keywords named.
constexpr VersionedWord kTable224[] = {
    {"alias", TokenKind::kKwAlias},
    {"always_comb", TokenKind::kKwAlwaysComb},
    {"always_ff", TokenKind::kKwAlwaysFF},
    {"always_latch", TokenKind::kKwAlwaysLatch},
    {"assert", TokenKind::kKwAssert},
    {"assume", TokenKind::kKwAssume},
    {"before", TokenKind::kKwBefore},
    {"bind", TokenKind::kKwBind},
    {"bins", TokenKind::kKwBins},
    {"binsof", TokenKind::kKwBinsof},
    {"bit", TokenKind::kKwBit},
    {"break", TokenKind::kKwBreak},
    {"byte", TokenKind::kKwByte},
    {"chandle", TokenKind::kKwChandle},
    {"class", TokenKind::kKwClass},
    {"clocking", TokenKind::kKwClocking},
    {"const", TokenKind::kKwConst},
    {"constraint", TokenKind::kKwConstraint},
    {"context", TokenKind::kKwContext},
    {"continue", TokenKind::kKwContinue},
    {"cover", TokenKind::kKwCover},
    {"covergroup", TokenKind::kKwCovergroup},
    {"coverpoint", TokenKind::kKwCoverpoint},
    {"cross", TokenKind::kKwCross},
    {"dist", TokenKind::kKwDist},
    {"do", TokenKind::kKwDo},
    {"endclass", TokenKind::kKwEndclass},
    {"endclocking", TokenKind::kKwEndclocking},
    {"endgroup", TokenKind::kKwEndgroup},
    {"endinterface", TokenKind::kKwEndinterface},
    {"endpackage", TokenKind::kKwEndpackage},
    {"endprogram", TokenKind::kKwEndprogram},
    {"endproperty", TokenKind::kKwEndproperty},
    {"endsequence", TokenKind::kKwEndsequence},
    {"enum", TokenKind::kKwEnum},
    {"expect", TokenKind::kKwExpect},
    {"export", TokenKind::kKwExport},
    {"extends", TokenKind::kKwExtends},
    {"extern", TokenKind::kKwExtern},
    {"final", TokenKind::kKwFinal},
    {"first_match", TokenKind::kKwFirstMatch},
    {"foreach", TokenKind::kKwForeach},
    {"forkjoin", TokenKind::kKwForkjoin},
    {"iff", TokenKind::kKwIff},
    {"ignore_bins", TokenKind::kKwIgnoreBins},
    {"illegal_bins", TokenKind::kKwIllegalBins},
    {"import", TokenKind::kKwImport},
    {"inside", TokenKind::kKwInside},
    {"int", TokenKind::kKwInt},
    {"interface", TokenKind::kKwInterface},
    {"intersect", TokenKind::kKwIntersect},
    {"join_any", TokenKind::kKwJoinAny},
    {"join_none", TokenKind::kKwJoinNone},
    {"local", TokenKind::kKwLocal},
    {"logic", TokenKind::kKwLogic},
    {"longint", TokenKind::kKwLongint},
    {"matches", TokenKind::kKwMatches},
    {"modport", TokenKind::kKwModport},
    {"new", TokenKind::kKwNew},
    {"null", TokenKind::kKwNull},
    {"package", TokenKind::kKwPackage},
    {"packed", TokenKind::kKwPacked},
    {"priority", TokenKind::kKwPriority},
    {"program", TokenKind::kKwProgram},
    {"property", TokenKind::kKwProperty},
    {"protected", TokenKind::kKwProtected},
    {"pure", TokenKind::kKwPure},
    {"rand", TokenKind::kKwRand},
    {"randc", TokenKind::kKwRandc},
    {"randcase", TokenKind::kKwRandcase},
    {"randsequence", TokenKind::kKwRandsequence},
    {"ref", TokenKind::kKwRef},
    {"return", TokenKind::kKwReturn},
    {"sequence", TokenKind::kKwSequence},
    {"shortint", TokenKind::kKwShortint},
    {"shortreal", TokenKind::kKwShortreal},
    {"solve", TokenKind::kKwSolve},
    {"static", TokenKind::kKwStatic},
    {"string", TokenKind::kKwString},
    {"struct", TokenKind::kKwStruct},
    {"super", TokenKind::kKwSuper},
    {"tagged", TokenKind::kKwTagged},
    {"this", TokenKind::kKwThis},
    {"throughout", TokenKind::kKwThroughout},
    {"timeprecision", TokenKind::kKwTimeprecision},
    {"timeunit", TokenKind::kKwTimeunit},
    {"type", TokenKind::kKwType},
    {"typedef", TokenKind::kKwTypedef},
    {"union", TokenKind::kKwUnion},
    {"unique", TokenKind::kKwUnique},
    {"var", TokenKind::kKwVar},
    {"virtual", TokenKind::kKwVirtual},
    {"void", TokenKind::kKwVoid},
    {"wait_order", TokenKind::kKwWaitOrder},
    {"wildcard", TokenKind::kKwWildcard},
    {"with", TokenKind::kKwWith},
    {"within", TokenKind::kKwWithin},
};

// Table 22-2, the second included list, with its keywords named.
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

// The ten of Table 22-2 that the configuration-free companion list drops.
constexpr const char* kConfigurationWords[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

// Table 22-1, the first included list.
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
// and not that of the SystemVerilog standard on either side of it.
TEST(KeywordVersionPreprocessing, SystemVerilog2009DirectiveEmitsItsOwnMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2009\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002009);

  for (const char* neighbour : {"1800-2005", "1800-2012"}) {
    PreprocFixture other_fixture;
    auto other = Preprocess(std::string("`begin_keywords \"") + neighbour +
                                "\"\nx\n`end_keywords\n",
                            other_fixture);
    auto other_pos = other.find(kKeywordMarker);
    ASSERT_NE(other_pos, std::string::npos) << neighbour;
    EXPECT_NE(out[pos + 1], other[other_pos + 1]) << neighbour;
  }
}

// The negative for the specifier, driven from real source rather than from a
// direct call on the string. Only the exact spelling names this list, so a word
// differing from it by its year or by a separator selects nothing and leaves
// the source that follows to be read under whatever list was already in force.
// `interconnect` is what makes that visible: this version leaves it an ordinary
// identifier while the default list reserves it, so the kind it lexes with says
// which of the two governed the region.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009OnlyTheExactSpecifierSelectsIt) {
  // The spelling this subclause defines: the word is free.
  EXPECT_EQ(KindAfterSpecifier("1800-2009", "interconnect"),
            TokenKind::kIdentifier);

  const char* kNearMisses[] = {
      "1800-2008", "1800-2010", "1800_2009", "18002009", "1364-2009",
  };
  for (const char* spec : kNearMisses) {
    EXPECT_EQ(KindAfterSpecifier(spec, "interconnect"),
              TokenKind::kKwInterconnect)
        << spec << " names no version, so this list was never put in force";
  }
}

// The first included list carried through a real region, swept whole. Each word
// arrives at the lexer holding the keyword it holds under the list it comes
// from, which is what including the identifiers of "1364-1995" amounts to once
// the directive is in force.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto here = KindInRegion("1800-2009", word);
    EXPECT_NE(here, TokenKind::kIdentifier) << word << " is a reserved word";
    EXPECT_EQ(here, KindInRegion("1364-1995", word))
        << word << " keeps its meaning from the list it comes from";
  }
}

// The second included list the same way, and with the keyword named outright.
// The leg under "1364-1995" is what makes each of these an inclusion: under the
// earlier list the very same word is an ordinary identifier. The ten
// configuration words carry a second leg of their own, under the
// configuration-free companion list that drops exactly them -- which is how the
// region shows that this version inherits "1364-2001" whole rather than its
// reduced companion.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const auto& word : kTable222) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-1995", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of the second included list";
  }

  for (const char* word : kConfigurationWords) {
    EXPECT_NE(KindInRegion("1800-2009", word), TokenKind::kIdentifier) << word;
    EXPECT_EQ(KindInRegion("1364-2001-noconfig", word), TokenKind::kIdentifier)
        << word << " is what the configuration-free companion list drops";
  }
}

// The third included list, which holds one word. Both of the lists that one is
// built on leave it an identifier, so its being a keyword here traces to the
// third inclusion and to nothing else.
TEST(KeywordVersionPreprocessing, SystemVerilog2009ReservesTheVerilog2005Word) {
  EXPECT_EQ(KindInRegion("1800-2009", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2001", "uwire"), TokenKind::kIdentifier);
  EXPECT_EQ(KindInRegion("1364-1995", "uwire"), TokenKind::kIdentifier);
}

// The fourth included list driven through the directive, swept whole. Each
// entry reaches the lexer as the keyword it names, and under "1364-2005" -- the
// union of the three lists that one is itself built on -- the very same word
// arrives as an ordinary identifier, so the inclusion is the fourth one rather
// than anything earlier.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009ReservesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kTable224), 97u);
  for (const auto& word : kTable224) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-2005", word.text), TokenKind::kIdentifier)
        << word.text << " comes from the fourth included list";
  }
}

// Table 22-5 driven through the directive, swept whole and word by word. Each
// entry reaches the lexer as the keyword it names, and the paired leg under
// "1800-2005" -- the union of everything this version includes -- has the very
// same word arriving as an ordinary identifier. That pairing is the claim: the
// words are additions of this version_specifier rather than anything inherited.
TEST(KeywordVersionPreprocessing, SystemVerilog2009ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kTable225), 23u);
  for (const auto& word : kTable225) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1800-2005", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of this version, not an inheritance";
  }
}

// The negative the five tables imply: a word none of them lists reaches the
// lexer as an ordinary identifier under this version, however firmly the next
// standard reserves it. Each is paired against that later specifier so the
// words are seen to be later ones rather than merely unknown ones.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009LeavesLaterWordsAsIdentifiers) {
  struct LaterWord {
    const char* text;
    TokenKind kind;
  };
  const LaterWord kLater[] = {
      {"implements", TokenKind::kKwImplements},
      {"interconnect", TokenKind::kKwInterconnect},
      {"nettype", TokenKind::kKwNettype},
      {"soft", TokenKind::kKwSoft},
  };
  for (const auto& word : kLater) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), TokenKind::kIdentifier)
        << word.text << " is outside the five tables this version names";
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind)
        << word.text << " is reserved by the version after this one";
  }
}

}  // namespace
