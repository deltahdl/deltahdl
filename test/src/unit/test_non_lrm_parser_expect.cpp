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

// No clause of IEEE 1800-2023 says how a parser reports a token it did not
// find, so these cases cover Parser::Expect on its own terms. Every caller of
// it is parsing a different production of the syntax and so enforcing a
// different rule, which is why the clause the report names is a parameter: the
// one sentence Expect writes is shared by every caller, and the clause is not.
//
// Expect is private to Parser, and what it reports is what these cases are
// about, so they reach it through the struct Parser names as a friend.
struct ParserExpectAccess {
  static Token Expect(Parser& parser, TokenKind kind, Clause clause) {
    return parser.Expect(kind, clause);
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

  void ExpectSemicolon(Clause clause) {
    ParserExpectAccess::Expect(parser, TokenKind::kSemicolon, clause);
  }
};

TEST(ExpectWithAClause, ReportsTheClauseTheCallerGave) {
  // The clause reaches the record from the call site, so a caller that has
  // read its production against the standard can say which rule it enforces.
  ExpectFixture f;
  f.ExpectSemicolon(Clause("23.2.2"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().clause, "23.2.2");
}

TEST(ExpectWithAClause, MessageIsUnchanged) {
  // The clause goes beside the sentence rather than into it, so two calls
  // differing only in the clause they name read out the same sentence. Without
  // this, a caller naming a clause would get a message no other caller writes.
  ExpectFixture named;
  named.ExpectSemicolon(Clause("23.2.2"));
  ExpectFixture unread;
  unread.ExpectSemicolon(Clause::Unread());

  ASSERT_EQ(named.diag.Diagnostics().size(), 1u);
  ASSERT_EQ(unread.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(named.diag.Diagnostics().front().message,
            unread.diag.Diagnostics().front().message);
}

TEST(ExpectWithAnUnreadClause, RecordsAnEmptyClause) {
  // A caller that cannot yet name its production gets a record naming no
  // clause, rather than one naming a clause Expect chose for it. Every call
  // site that has not been read against the standard depends on that: a clause
  // Expect substituted would be right for one caller and wrong for the rest.
  ExpectFixture f;
  f.ExpectSemicolon(Clause::Unread());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().clause, "");
}

}  // namespace
}  // namespace delta
