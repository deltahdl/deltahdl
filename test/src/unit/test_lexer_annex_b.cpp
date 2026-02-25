// §B

#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

namespace {

// §B Table B.1 — every keyword paired with its expected TokenKind.
struct KwEntry {
  const char* text;
  TokenKind expected;
};

static const KwEntry kTableB1[] = {
    {"accept_on", TokenKind::kKwAcceptOn},
    {"alias", TokenKind::kKwAlias},
    {"always", TokenKind::kKwAlways},
    {"always_comb", TokenKind::kKwAlwaysComb},
    {"always_ff", TokenKind::kKwAlwaysFF},
    {"always_latch", TokenKind::kKwAlwaysLatch},
    {"and", TokenKind::kKwAnd},
    {"assert", TokenKind::kKwAssert},
    {"assign", TokenKind::kKwAssign},
    {"assume", TokenKind::kKwAssume},
    {"automatic", TokenKind::kKwAutomatic},
    {"before", TokenKind::kKwBefore},
    {"begin", TokenKind::kKwBegin},
    {"bind", TokenKind::kKwBind},
    {"bins", TokenKind::kKwBins},
    {"binsof", TokenKind::kKwBinsof},
    {"bit", TokenKind::kKwBit},
    {"break", TokenKind::kKwBreak},
    {"buf", TokenKind::kKwBuf},
    {"bufif0", TokenKind::kKwBufif0},
    {"bufif1", TokenKind::kKwBufif1},
    {"byte", TokenKind::kKwByte},
    {"case", TokenKind::kKwCase},
    {"casex", TokenKind::kKwCasex},
    {"casez", TokenKind::kKwCasez},
    {"cell", TokenKind::kKwCell},
    {"chandle", TokenKind::kKwChandle},
    {"checker", TokenKind::kKwChecker},
    {"class", TokenKind::kKwClass},
    {"clocking", TokenKind::kKwClocking},
    {"cmos", TokenKind::kKwCmos},
    {"config", TokenKind::kKwConfig},
    {"const", TokenKind::kKwConst},
    {"constraint", TokenKind::kKwConstraint},
    {"context", TokenKind::kKwContext},
    {"continue", TokenKind::kKwContinue},
    {"cover", TokenKind::kKwCover},
    {"covergroup", TokenKind::kKwCovergroup},
    {"coverpoint", TokenKind::kKwCoverpoint},
    {"cross", TokenKind::kKwCross},
    {"deassign", TokenKind::kKwDeassign},
    {"default", TokenKind::kKwDefault},
    {"defparam", TokenKind::kKwDefparam},
    {"design", TokenKind::kKwDesign},
    {"disable", TokenKind::kKwDisable},
    {"dist", TokenKind::kKwDist},
    {"do", TokenKind::kKwDo},
    {"edge", TokenKind::kKwEdge},
    {"else", TokenKind::kKwElse},
    {"end", TokenKind::kKwEnd},
    {"endcase", TokenKind::kKwEndcase},
    {"endchecker", TokenKind::kKwEndchecker},
    {"endclass", TokenKind::kKwEndclass},
    {"endclocking", TokenKind::kKwEndclocking},
    {"endconfig", TokenKind::kKwEndconfig},
    {"endfunction", TokenKind::kKwEndfunction},
    {"endgenerate", TokenKind::kKwEndgenerate},
    {"endgroup", TokenKind::kKwEndgroup},
    {"endinterface", TokenKind::kKwEndinterface},
    {"endmodule", TokenKind::kKwEndmodule},
    {"endpackage", TokenKind::kKwEndpackage},
    {"endprimitive", TokenKind::kKwEndprimitive},
    {"endprogram", TokenKind::kKwEndprogram},
    {"endproperty", TokenKind::kKwEndproperty},
    {"endsequence", TokenKind::kKwEndsequence},
    {"endspecify", TokenKind::kKwEndspecify},
    {"endtable", TokenKind::kKwEndtable},
    {"endtask", TokenKind::kKwEndtask},
    {"enum", TokenKind::kKwEnum},
    {"event", TokenKind::kKwEvent},
    {"eventually", TokenKind::kKwEventually},
    {"expect", TokenKind::kKwExpect},
    {"export", TokenKind::kKwExport},
    {"extends", TokenKind::kKwExtends},
    {"extern", TokenKind::kKwExtern},
    {"final", TokenKind::kKwFinal},
    {"first_match", TokenKind::kKwFirstMatch},
    {"for", TokenKind::kKwFor},
    {"force", TokenKind::kKwForce},
    {"foreach", TokenKind::kKwForeach},
    {"forever", TokenKind::kKwForever},
    {"fork", TokenKind::kKwFork},
    {"forkjoin", TokenKind::kKwForkjoin},
    {"function", TokenKind::kKwFunction},
    {"generate", TokenKind::kKwGenerate},
    {"genvar", TokenKind::kKwGenvar},
    {"global", TokenKind::kKwGlobal},
    {"highz0", TokenKind::kKwHighz0},
    {"highz1", TokenKind::kKwHighz1},
    {"if", TokenKind::kKwIf},
    {"iff", TokenKind::kKwIff},
    {"ifnone", TokenKind::kKwIfnone},
    {"ignore_bins", TokenKind::kKwIgnoreBins},
    {"illegal_bins", TokenKind::kKwIllegalBins},
    {"implements", TokenKind::kKwImplements},
    {"implies", TokenKind::kKwImplies},
    {"import", TokenKind::kKwImport},
    {"incdir", TokenKind::kKwIncdir},
    {"include", TokenKind::kKwInclude},
    {"initial", TokenKind::kKwInitial},
    {"inout", TokenKind::kKwInout},
    {"input", TokenKind::kKwInput},
    {"inside", TokenKind::kKwInside},
    {"instance", TokenKind::kKwInstance},
    {"int", TokenKind::kKwInt},
    {"integer", TokenKind::kKwInteger},
    {"interconnect", TokenKind::kKwInterconnect},
    {"interface", TokenKind::kKwInterface},
    {"intersect", TokenKind::kKwIntersect},
    {"join", TokenKind::kKwJoin},
    {"join_any", TokenKind::kKwJoinAny},
    {"join_none", TokenKind::kKwJoinNone},
    {"large", TokenKind::kKwLarge},
    {"let", TokenKind::kKwLet},
    {"liblist", TokenKind::kKwLiblist},
    {"library", TokenKind::kKwLibrary},
    {"local", TokenKind::kKwLocal},
    {"localparam", TokenKind::kKwLocalparam},
    {"logic", TokenKind::kKwLogic},
    {"longint", TokenKind::kKwLongint},
    {"macromodule", TokenKind::kKwMacromodule},
    {"matches", TokenKind::kKwMatches},
    {"medium", TokenKind::kKwMedium},
    {"modport", TokenKind::kKwModport},
    {"module", TokenKind::kKwModule},
    {"nand", TokenKind::kKwNand},
    {"negedge", TokenKind::kKwNegedge},
    {"nettype", TokenKind::kKwNettype},
    {"new", TokenKind::kKwNew},
    {"nexttime", TokenKind::kKwNexttime},
    {"nmos", TokenKind::kKwNmos},
    {"nor", TokenKind::kKwNor},
    {"noshowcancelled", TokenKind::kKwNoshowcancelled},
    {"not", TokenKind::kKwNot},
    {"notif0", TokenKind::kKwNotif0},
    {"notif1", TokenKind::kKwNotif1},
    {"null", TokenKind::kKwNull},
    {"or", TokenKind::kKwOr},
    {"output", TokenKind::kKwOutput},
    {"package", TokenKind::kKwPackage},
    {"packed", TokenKind::kKwPacked},
    {"parameter", TokenKind::kKwParameter},
    {"pmos", TokenKind::kKwPmos},
    {"posedge", TokenKind::kKwPosedge},
    {"primitive", TokenKind::kKwPrimitive},
    {"priority", TokenKind::kKwPriority},
    {"program", TokenKind::kKwProgram},
    {"property", TokenKind::kKwProperty},
    {"protected", TokenKind::kKwProtected},
    {"pull0", TokenKind::kKwPull0},
    {"pull1", TokenKind::kKwPull1},
    {"pulldown", TokenKind::kKwPulldown},
    {"pullup", TokenKind::kKwPullup},
    {"pulsestyle_ondetect", TokenKind::kKwPulsestyleOndetect},
    {"pulsestyle_onevent", TokenKind::kKwPulsestyleOnevent},
    {"pure", TokenKind::kKwPure},
    {"rand", TokenKind::kKwRand},
    {"randc", TokenKind::kKwRandc},
    {"randcase", TokenKind::kKwRandcase},
    {"randsequence", TokenKind::kKwRandsequence},
    {"rcmos", TokenKind::kKwRcmos},
    {"real", TokenKind::kKwReal},
    {"realtime", TokenKind::kKwRealtime},
    {"ref", TokenKind::kKwRef},
    {"reg", TokenKind::kKwReg},
    {"reject_on", TokenKind::kKwRejectOn},
    {"release", TokenKind::kKwRelease},
    {"repeat", TokenKind::kKwRepeat},
    {"restrict", TokenKind::kKwRestrict},
    {"return", TokenKind::kKwReturn},
    {"rnmos", TokenKind::kKwRnmos},
    {"rpmos", TokenKind::kKwRpmos},
    {"rtran", TokenKind::kKwRtran},
    {"rtranif0", TokenKind::kKwRtranif0},
    {"rtranif1", TokenKind::kKwRtranif1},
    {"s_always", TokenKind::kKwSAlways},
    {"s_eventually", TokenKind::kKwSEventually},
    {"s_nexttime", TokenKind::kKwSNexttime},
    {"s_until", TokenKind::kKwSUntil},
    {"s_until_with", TokenKind::kKwSUntilWith},
    {"scalared", TokenKind::kKwScalared},
    {"sequence", TokenKind::kKwSequence},
    {"shortint", TokenKind::kKwShortint},
    {"shortreal", TokenKind::kKwShortreal},
    {"showcancelled", TokenKind::kKwShowcancelled},
    {"signed", TokenKind::kKwSigned},
    {"small", TokenKind::kKwSmall},
    {"soft", TokenKind::kKwSoft},
    {"solve", TokenKind::kKwSolve},
    {"specify", TokenKind::kKwSpecify},
    {"specparam", TokenKind::kKwSpecparam},
    {"static", TokenKind::kKwStatic},
    {"string", TokenKind::kKwString},
    {"strong", TokenKind::kKwStrong},
    {"strong0", TokenKind::kKwStrong0},
    {"strong1", TokenKind::kKwStrong1},
    {"struct", TokenKind::kKwStruct},
    {"super", TokenKind::kKwSuper},
    {"supply0", TokenKind::kKwSupply0},
    {"supply1", TokenKind::kKwSupply1},
    {"sync_accept_on", TokenKind::kKwSyncAcceptOn},
    {"sync_reject_on", TokenKind::kKwSyncRejectOn},
    {"table", TokenKind::kKwTable},
    {"tagged", TokenKind::kKwTagged},
    {"task", TokenKind::kKwTask},
    {"this", TokenKind::kKwThis},
    {"throughout", TokenKind::kKwThroughout},
    {"time", TokenKind::kKwTime},
    {"timeprecision", TokenKind::kKwTimeprecision},
    {"timeunit", TokenKind::kKwTimeunit},
    {"tran", TokenKind::kKwTran},
    {"tranif0", TokenKind::kKwTranif0},
    {"tranif1", TokenKind::kKwTranif1},
    {"tri", TokenKind::kKwTri},
    {"tri0", TokenKind::kKwTri0},
    {"tri1", TokenKind::kKwTri1},
    {"triand", TokenKind::kKwTriand},
    {"trior", TokenKind::kKwTrior},
    {"trireg", TokenKind::kKwTrireg},
    {"type", TokenKind::kKwType},
    {"typedef", TokenKind::kKwTypedef},
    {"union", TokenKind::kKwUnion},
    {"unique", TokenKind::kKwUnique},
    {"unique0", TokenKind::kKwUnique0},
    {"unsigned", TokenKind::kKwUnsigned},
    {"until", TokenKind::kKwUntil},
    {"until_with", TokenKind::kKwUntilWith},
    {"untyped", TokenKind::kKwUntyped},
    {"use", TokenKind::kKwUse},
    {"uwire", TokenKind::kKwUwire},
    {"var", TokenKind::kKwVar},
    {"vectored", TokenKind::kKwVectored},
    {"virtual", TokenKind::kKwVirtual},
    {"void", TokenKind::kKwVoid},
    {"wait", TokenKind::kKwWait},
    {"wait_order", TokenKind::kKwWaitOrder},
    {"wand", TokenKind::kKwWand},
    {"weak", TokenKind::kKwWeak},
    {"weak0", TokenKind::kKwWeak0},
    {"weak1", TokenKind::kKwWeak1},
    {"while", TokenKind::kKwWhile},
    {"wildcard", TokenKind::kKwWildcard},
    {"wire", TokenKind::kKwWire},
    {"with", TokenKind::kKwWith},
    {"within", TokenKind::kKwWithin},
    {"wor", TokenKind::kKwWor},
    {"xnor", TokenKind::kKwXnor},
    {"xor", TokenKind::kKwXor},
};

static constexpr size_t kTableB1Count = sizeof(kTableB1) / sizeof(kTableB1[0]);

// ------------------------------------------------------------------
// B.1  Completeness — Table B.1 contains exactly 248 keywords
// ------------------------------------------------------------------

TEST(LexerAnnexB, TableB1CountIs248) { EXPECT_EQ(kTableB1Count, 248u); }

// ------------------------------------------------------------------
// B.2  Reservation — every Table B.1 keyword lexes as a keyword
// ------------------------------------------------------------------

TEST(LexerAnnexB, AllKeywordsAreReserved) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto tokens = Lex(kTableB1[i].text);
    ASSERT_GE(tokens.size(), 2u) << "keyword: " << kTableB1[i].text;
    EXPECT_NE(tokens[0].kind, TokenKind::kIdentifier)
        << kTableB1[i].text << " should be a keyword, not an identifier";
  }
}

// ------------------------------------------------------------------
// B.3  Specific TokenKind — each keyword maps to its correct token
// ------------------------------------------------------------------

TEST(LexerAnnexB, EachKeywordMapsToCorrectTokenKind) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto tokens = Lex(kTableB1[i].text);
    ASSERT_GE(tokens.size(), 2u) << "keyword: " << kTableB1[i].text;
    EXPECT_EQ(tokens[0].kind, kTableB1[i].expected)
        << kTableB1[i].text << " mapped to wrong TokenKind";
  }
}

// ------------------------------------------------------------------
// B.4  LookupKeyword API — direct table validation (not through lexer)
// ------------------------------------------------------------------

TEST(LexerAnnexB, LookupKeywordReturnsCorrectTokenKind) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto result = LookupKeyword(kTableB1[i].text);
    ASSERT_TRUE(result.has_value())
        << kTableB1[i].text << " not in keyword table";
    EXPECT_EQ(*result, kTableB1[i].expected)
        << kTableB1[i].text << " LookupKeyword returned wrong TokenKind";
  }
}

// ------------------------------------------------------------------
// B.5  Case sensitivity (§5.6.2) — keywords are lowercase only
// ------------------------------------------------------------------

TEST(LexerAnnexB, UppercaseIsNotKeyword) {
  const char* const kSamples[] = {
      "MODULE", "WIRE",    "REG",    "INPUT",   "OUTPUT", "ALWAYS", "IF",
      "ELSE",   "BEGIN",   "END",    "CLASS",   "LOGIC",  "INT",    "FUNCTION",
      "TASK",   "PACKAGE", "IMPORT", "TYPEDEF", "ENUM",   "STRUCT",
  };
  for (const char* upper : kSamples) {
    auto tokens = Lex(upper);
    ASSERT_GE(tokens.size(), 2u) << "upper: " << upper;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << upper << " (uppercase) should be an identifier, not a keyword";
  }
}

TEST(LexerAnnexB, MixedCaseIsNotKeyword) {
  const char* const kSamples[] = {
      "Module",  "Wire",     "Reg",    "Input",      "Output",
      "Always",  "Begin",    "End",    "Class",      "Logic",
      "Int",     "Function", "Task",   "Package",    "Import",
      "Typedef", "Enum",     "Struct", "AlwaysComb", "AlwaysFF",
  };
  for (const char* mixed : kSamples) {
    auto tokens = Lex(mixed);
    ASSERT_GE(tokens.size(), 2u) << "mixed: " << mixed;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << mixed << " (mixed case) should be an identifier, not a keyword";
  }
}

// ------------------------------------------------------------------
// B.6  Escape mechanism (§5.6.2) — escaped keywords become identifiers
// ------------------------------------------------------------------

TEST(LexerAnnexB, EscapedKeywordsAreIdentifiers) {
  const char* const kSamples[] = {
      "module",   "wire",     "reg",        "input",      "output",  "always",
      "if",       "else",     "begin",      "end",        "class",   "logic",
      "int",      "function", "task",       "package",    "import",  "typedef",
      "enum",     "struct",   "interface",  "program",    "checker", "clocking",
      "property", "sequence", "covergroup", "constraint", "assert",  "assume",
  };
  for (const char* kw : kSamples) {
    // Escaped identifiers: backslash + text + whitespace terminator
    std::string escaped = std::string("\\") + kw + " ";
    auto tokens = Lex(escaped);
    ASSERT_GE(tokens.size(), 2u) << "escaped: " << kw;
    EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier)
        << "\\" << kw << " should be an escaped identifier, not a keyword";
  }
}

// ------------------------------------------------------------------
// B.7  Non-keywords — words not in Table B.1 are identifiers
// ------------------------------------------------------------------

TEST(LexerAnnexB, NonKeywordsAreIdentifiers) {
  const char* const kNonKeywords[] = {
      "foo",   "bar",   "my_signal", "data_in", "clk",        "reset",
      "valid", "ready", "counter",   "state",   "next_state", "addr",
  };
  for (const char* id : kNonKeywords) {
    auto result = LookupKeyword(id);
    EXPECT_FALSE(result.has_value()) << id << " should not be a keyword";
    auto tokens = Lex(id);
    ASSERT_GE(tokens.size(), 2u) << "id: " << id;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << id << " should lex as an identifier";
  }
}

// ------------------------------------------------------------------
// B.8  Table B.1 is in alphabetical order
// ------------------------------------------------------------------

TEST(LexerAnnexB, TableB1IsAlphabetical) {
  for (size_t i = 1; i < kTableB1Count; ++i) {
    EXPECT_LT(std::string_view(kTableB1[i - 1].text),
              std::string_view(kTableB1[i].text))
        << "Table B.1 entry " << i - 1 << " (" << kTableB1[i - 1].text
        << ") should precede entry " << i << " (" << kTableB1[i].text << ")";
  }
}

// ------------------------------------------------------------------
// B.9  Each keyword produces exactly one token (plus EOF)
// ------------------------------------------------------------------

TEST(LexerAnnexB, EachKeywordProducesOneToken) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto tokens = Lex(kTableB1[i].text);
    EXPECT_EQ(tokens.size(), 2u)
        << kTableB1[i].text << " should produce exactly one token plus EOF";
    EXPECT_EQ(tokens.back().kind, TokenKind::kEof)
        << kTableB1[i].text << " should end with EOF";
  }
}

// ------------------------------------------------------------------
// B.10 Keyword text preservation — lexer preserves original text
// ------------------------------------------------------------------

TEST(LexerAnnexB, KeywordTextIsPreserved) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto tokens = Lex(kTableB1[i].text);
    ASSERT_GE(tokens.size(), 2u) << "keyword: " << kTableB1[i].text;
    EXPECT_EQ(tokens[0].text, kTableB1[i].text)
        << kTableB1[i].text << " text not preserved";
  }
}

// ------------------------------------------------------------------
// B.11 No duplicate TokenKind values across Table B.1
// ------------------------------------------------------------------

TEST(LexerAnnexB, NoDuplicateTokenKinds) {
  std::set<TokenKind> seen;
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto [it, inserted] = seen.insert(kTableB1[i].expected);
    EXPECT_TRUE(inserted) << kTableB1[i].text << " has a duplicate TokenKind";
  }
  EXPECT_EQ(seen.size(), kTableB1Count);
}

}  // namespace
