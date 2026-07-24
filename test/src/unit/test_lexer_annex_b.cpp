#include <gtest/gtest.h>

#include <cctype>
#include <string>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

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

TEST(KeywordListLexing, ReservedKeywordCountIs248) {
  EXPECT_EQ(kTableB1Count, 248u);
}

TEST(KeywordListLexing, EachKeywordMapsToCorrectTokenKind) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto tokens = Lex(kTableB1[i].text);
    ASSERT_GE(tokens.size(), 2u) << "keyword: " << kTableB1[i].text;
    EXPECT_EQ(tokens[0].kind, kTableB1[i].expected)
        << kTableB1[i].text << " mapped to wrong TokenKind";
  }
}

TEST(KeywordListLexing, LookupKeywordReturnsCorrectTokenKind) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto result = LookupKeyword(kTableB1[i].text);
    ASSERT_TRUE(result.has_value())
        << kTableB1[i].text << " not in keyword table";
    EXPECT_EQ(result.value_or(TokenKind::kError), kTableB1[i].expected)
        << kTableB1[i].text << " LookupKeyword returned wrong TokenKind";
  }
}

TEST(KeywordListLexing, ReservedKeywordListIsAlphabetical) {
  for (size_t i = 1; i < kTableB1Count; ++i) {
    EXPECT_LT(std::string_view(kTableB1[i - 1].text),
              std::string_view(kTableB1[i].text))
        << "Table B.1 entry " << i - 1 << " (" << kTableB1[i - 1].text
        << ") should precede entry " << i << " (" << kTableB1[i].text << ")";
  }
}

TEST(KeywordListLexing, EachKeywordProducesOneToken) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto tokens = Lex(kTableB1[i].text);
    EXPECT_EQ(tokens.size(), 2u)
        << kTableB1[i].text << " should produce exactly one token plus EOF";
    EXPECT_EQ(tokens.back().kind, TokenKind::kEof)
        << kTableB1[i].text << " should end with EOF";
  }
}

TEST(KeywordListLexing, KeywordTextIsPreserved) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto tokens = Lex(kTableB1[i].text);
    ASSERT_GE(tokens.size(), 2u) << "keyword: " << kTableB1[i].text;
    EXPECT_EQ(tokens[0].text, kTableB1[i].text)
        << kTableB1[i].text << " text not preserved";
  }
}

// The other half of "the list is exactly this long". The token kinds the
// reserved words map to occupy one unbroken run of the token enumeration, and
// Table B.1's words land inside it and nowhere else. A run of exactly as many
// values as the annex prints words, entered by that many distinct kinds (the
// test above), leaves no kind over for a word the annex does not list -- which
// is the direction a fixed count of table entries cannot establish on its own.
TEST(KeywordListLexing, TableB1FillsTheWholeKeywordTokenKindRange) {
  constexpr auto kFirstKeywordKind = static_cast<int>(TokenKind::kKwModule);
  constexpr auto kLastKeywordKind = static_cast<int>(TokenKind::kKwXor);
  EXPECT_EQ(kLastKeywordKind - kFirstKeywordKind + 1,
            static_cast<int>(kTableB1Count))
      << "the keyword token kinds should number what Table B.1 lists";
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto kind = static_cast<int>(kTableB1[i].expected);
    EXPECT_GE(kind, kFirstKeywordKind) << kTableB1[i].text;
    EXPECT_LE(kind, kLastKeywordKind) << kTableB1[i].text;
  }
}

TEST(KeywordListLexing, NoDuplicateTokenKinds) {
  std::set<TokenKind> seen;
  for (size_t i = 0; i < kTableB1Count; ++i) {
    auto [it, inserted] = seen.insert(kTableB1[i].expected);
    EXPECT_TRUE(inserted) << kTableB1[i].text << " has a duplicate TokenKind";
  }
  EXPECT_EQ(seen.size(), kTableB1Count);
}

// Boundary of the reservation rule: only the exact lowercase spellings in
// Table B.1 are reserved. A differently-cased spelling must fall through to an
// ordinary identifier, both at the keyword-lookup layer and through the lexer.
TEST(KeywordListLexing, KeywordsAreCaseSensitive) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string upper(kTableB1[i].text);
    for (char& c : upper) {
      c = static_cast<char>(std::toupper(static_cast<unsigned char>(c)));
    }
    ASSERT_NE(upper, std::string(kTableB1[i].text))
        << "every keyword has a letter to upcase";
    EXPECT_FALSE(LookupKeyword(upper).has_value())
        << upper << " must not be reserved; keywords are case-sensitive";
    auto tokens = Lex(upper);
    ASSERT_GE(tokens.size(), 2u) << "input: " << upper;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << upper << " should lex as an identifier, not a keyword";
  }
}

// Reservation matches a complete token, not a leading substring. A keyword
// immediately followed by identifier characters is one ordinary identifier.
TEST(KeywordListLexing, KeywordWithIdentifierSuffixIsIdentifier) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string extended = std::string(kTableB1[i].text) + "_x";
    EXPECT_FALSE(LookupKeyword(extended).has_value())
        << extended << " must not be reserved";
    auto tokens = Lex(extended);
    ASSERT_GE(tokens.size(), 2u) << "input: " << extended;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << extended << " should lex as a single identifier";
    EXPECT_EQ(tokens[0].text, extended)
        << extended << " should be consumed as one token";
  }
}

// An underscore prefix yields a valid identifier whose spelling is not the
// reserved keyword, so it must not be treated as one.
TEST(KeywordListLexing, KeywordWithLeadingUnderscoreIsIdentifier) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string prefixed = "_" + std::string(kTableB1[i].text);
    EXPECT_FALSE(LookupKeyword(prefixed).has_value())
        << prefixed << " must not be reserved";
    auto tokens = Lex(prefixed);
    ASSERT_GE(tokens.size(), 2u) << "input: " << prefixed;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << prefixed << " should lex as an identifier";
  }
}

// Several listed words end in a digit, so a trailing digit is the near miss
// most likely to be mistaken for one of them. No entry is another entry with a
// '9' appended, which makes that suffix a spelling the table cannot contain.
TEST(KeywordListLexing, KeywordWithTrailingDigitIsIdentifier) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string suffixed = std::string(kTableB1[i].text) + "9";
    EXPECT_FALSE(LookupKeyword(suffixed).has_value())
        << suffixed << " must not be reserved";
    auto tokens = Lex(suffixed);
    ASSERT_GE(tokens.size(), 2u) << "input: " << suffixed;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << suffixed << " should lex as one identifier";
    EXPECT_EQ(tokens[0].text, suffixed)
        << suffixed << " should be consumed as one token";
  }
}

// A name may carry a '$' after its first character, so a listed word with one
// appended is a legal identifier whose spelling is not the reserved word. That
// is the near miss a scan keyed on letters and underscores alone would fumble.
TEST(KeywordListLexing, KeywordWithTrailingDollarIsIdentifier) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string suffixed = std::string(kTableB1[i].text) + "$";
    EXPECT_FALSE(LookupKeyword(suffixed).has_value())
        << suffixed << " must not be reserved";
    auto tokens = Lex(suffixed);
    ASSERT_GE(tokens.size(), 2u) << "input: " << suffixed;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << suffixed << " should lex as one identifier";
    EXPECT_EQ(tokens[0].text, suffixed)
        << suffixed << " should be consumed as one token";
  }
}

// Reservation is a property of the spelling alone, not of what surrounds it.
// Whitespace never separates the word from its neighbours here, so a scan that
// only recognized whitespace-delimited words would miss every one of these.
TEST(KeywordListLexing, KeywordIsReservedWhenAdjacentToPunctuation) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string src = "(" + std::string(kTableB1[i].text) + ")";
    auto tokens = Lex(src);
    ASSERT_EQ(tokens.size(), 4u) << "input: " << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kLParen) << src;
    EXPECT_EQ(tokens[1].kind, kTableB1[i].expected)
        << kTableB1[i].text << " should stay reserved between parentheses";
    EXPECT_EQ(tokens[2].kind, TokenKind::kRParen) << src;
  }
}

// A comment carries no token of its own, so the word that follows one begins a
// fresh scan and is reserved exactly as it would be at the start of a line.
TEST(KeywordListLexing, KeywordIsReservedImmediatelyAfterAComment) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string block = "/*c*/" + std::string(kTableB1[i].text);
    auto block_tokens = Lex(block);
    ASSERT_GE(block_tokens.size(), 2u) << "input: " << block;
    EXPECT_EQ(block_tokens[0].kind, kTableB1[i].expected)
        << kTableB1[i].text << " after a block comment";

    std::string line = "//c\n" + std::string(kTableB1[i].text);
    auto line_tokens = Lex(line);
    ASSERT_GE(line_tokens.size(), 2u) << "input: " << line;
    EXPECT_EQ(line_tokens[0].kind, kTableB1[i].expected)
        << kTableB1[i].text << " after a one-line comment";
  }
}

// The escape form is the boundary of the reservation: the very same letters,
// introduced by a backslash, are a user-chosen name again rather than the
// reserved word. The name the escape carries is the spelling without the
// backslash, which is what makes this the closest rejecting input there is.
TEST(KeywordListLexing, EscapedFormOfAKeywordIsAnIdentifier) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string escaped = "\\" + std::string(kTableB1[i].text) + " ";
    auto tokens = Lex(escaped);
    ASSERT_GE(tokens.size(), 2u) << "input: " << escaped;
    EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier)
        << escaped << " should lex as an escaped identifier";
    EXPECT_EQ(tokens[0].text, kTableB1[i].text)
        << escaped << " should carry the keyword spelling as its name";
  }
}

// Inside a string literal there is no identifier scan at all, so a listed word
// there is character data and yields one literal token.
TEST(KeywordListLexing, KeywordInsideAStringLiteralIsNotReserved) {
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string quoted = "\"" + std::string(kTableB1[i].text) + "\"";
    auto tokens = Lex(quoted);
    ASSERT_EQ(tokens.size(), 2u) << "input: " << quoted;
    EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral)
        << quoted << " should lex as a single string literal";
  }
}

// The reservation covers the table and stops there. These are names a reader
// could plausibly expect to be reserved -- built-in class and method names the
// language defines elsewhere, vocabulary from other hardware description
// languages, and plural or near-miss spellings of listed words -- and every one
// of them has to come back an ordinary identifier.
TEST(KeywordListLexing, VocabularyOutsideTableB1IsNotReserved) {
  const char* const kNotReserved[] = {
      // Names the language defines without reserving them.
      "randomize",
      "srandom",
      "mailbox",
      "semaphore",
      "process",
      "std",
      "option",
      "sample",
      "size",
      "delete",
      "exists",
      "num",
      "get_randstate",
      // Reserved words of other hardware description languages.
      "variable",
      "signal",
      "entity",
      "architecture",
      "component",
      "downto",
      // Near misses of listed words.
      "wired",
      "logics",
      "nettypes",
      "endmodules",
      "always_seq",
      "interfaces",
      "s_until_without",
      "join_all",
      "unique1",
      "weak2",
      "tri2",
      "assertion",
      // General-purpose vocabulary that is not on the list.
      "bool",
      "boolean",
      "true",
      "false",
      "byte_enable",
      "state",
  };
  for (const char* word : kNotReserved) {
    EXPECT_FALSE(LookupKeyword(word).has_value())
        << word << " is not on Table B.1 and must not be reserved";
    auto tokens = Lex(word);
    ASSERT_GE(tokens.size(), 2u) << "input: " << word;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << word << " should lex as an identifier";
    EXPECT_EQ(tokens[0].text, word) << word << " text not preserved";
  }
}

// Every word above is genuinely absent from the list this file checks, so the
// negative sweep cannot be quietly asserting something about a listed word.
TEST(KeywordListLexing, TheNonReservedVocabularyIsDisjointFromTableB1) {
  const char* const kNotReserved[] = {
      "randomize", "std",      "variable", "signal", "wired",
      "logics",    "join_all", "boolean",  "state",  "tri2",
  };
  for (const char* word : kNotReserved) {
    for (size_t i = 0; i < kTableB1Count; ++i) {
      EXPECT_NE(std::string_view(word), std::string_view(kTableB1[i].text))
          << word << " is on Table B.1 after all";
    }
  }
}

// The reservation applies to the language as a whole, not to one word at a
// time: the entire list run together as a single stream comes back as that
// many keyword tokens, in order, with nothing merged and nothing dropped.
TEST(KeywordListLexing, WholeListLexesAsThatManyKeywordsInOrder) {
  std::string all;
  for (size_t i = 0; i < kTableB1Count; ++i) {
    all += kTableB1[i].text;
    all += '\n';
  }
  auto tokens = Lex(all);
  ASSERT_EQ(tokens.size(), kTableB1Count + 1)
      << "one token per keyword plus EOF";
  for (size_t i = 0; i < kTableB1Count; ++i) {
    EXPECT_EQ(tokens[i].kind, kTableB1[i].expected)
        << kTableB1[i].text << " at stream position " << i;
    EXPECT_EQ(tokens[i].text, kTableB1[i].text) << "position " << i;
  }
  EXPECT_EQ(tokens.back().kind, TokenKind::kEof);
}

}  // namespace
