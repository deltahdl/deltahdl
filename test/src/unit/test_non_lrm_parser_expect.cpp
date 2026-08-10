#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/parser.h"

namespace delta {

// No subclause of IEEE 1800-2023 says how a parser reports a token it did not
// find, so these cases cover Parser::Expect on its own terms. Every caller of
// it is parsing a different production of the syntax and so enforcing a
// different rule, which is why the subclause the report names is a parameter:
// the one sentence Expect writes is shared by every caller, and the subclause
// is not.
//
// Expect is private to Parser, and what it reports is what these cases are
// about, so they reach it through the struct Parser names as a friend.
struct ParserExpectAccess {
  static Token Expect(Parser& parser, TokenKind kind, Subclause subclause) {
    return parser.Expect(kind, subclause);
  }
};

namespace {

// One source that does not hold the token every case asks for, so each call
// takes the reporting path rather than consuming a token and returning. The
// first token is the module keyword and the token asked for is a semicolon.
struct ExpectFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  uint32_t file_id = mgr.AddFile("m.sv", "module m;\n");
  Lexer lexer{mgr.FileContent(file_id), file_id, diag};
  Parser parser{lexer, arena, diag};

  void ExpectSemicolon(Subclause subclause) {
    ParserExpectAccess::Expect(parser, TokenKind::kSemicolon, subclause);
  }
};

TEST(ExpectWithASubclause, ReportsTheSubclauseTheCallerGave) {
  // The subclause reaches the record from the call site, so a caller that has
  // read its production against the standard can say which rule it enforces.
  ExpectFixture f;
  f.ExpectSemicolon(Subclause("23.2.2"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "23.2.2");
}

TEST(ExpectWithASubclause, MessageIsUnchanged) {
  // The subclause goes beside the sentence rather than into it, so two calls
  // differing only in the subclause they name read out the same sentence.
  // Without this, a caller naming a subclause would get a message no other
  // caller writes.
  ExpectFixture named;
  named.ExpectSemicolon(Subclause("23.2.2"));
  ExpectFixture unnamed;
  unnamed.ExpectSemicolon(Subclause::None());

  ASSERT_EQ(named.diag.Diagnostics().size(), 1u);
  ASSERT_EQ(unnamed.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(named.diag.Diagnostics().front().message,
            unnamed.diag.Diagnostics().front().message);
}

TEST(ExpectStatingNoRuleOfTheStandard, RecordsAnEmptySubclause) {
  // A caller whose production the standard states no rule about gets a record
  // naming no subclause, rather than one naming a subclause Expect chose for
  // it: a subclause Expect substituted would be right for one caller and wrong
  // for the rest.
  ExpectFixture f;
  f.ExpectSemicolon(Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "");
}

}  // namespace
}  // namespace delta
