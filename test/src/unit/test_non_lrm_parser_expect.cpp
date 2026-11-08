#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/parser.h"

namespace delta {

struct ParserExpectAccess {
  static Token Expect(Parser& parser, TokenKind kind, Subclause subclause) {
    return parser.Expect(kind, subclause);
  }
};

namespace {

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
  ExpectFixture f;
  f.ExpectSemicolon(Subclause("23.2.2"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "23.2.2");
}

TEST(ExpectWithASubclause, MessageIsUnchanged) {
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
  ExpectFixture f;
  f.ExpectSemicolon(Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "");
}

TEST(ExpectNamingTheTokenItFound, ReportNamesTheKeywordItFound) {
  ExpectFixture f;
  f.ExpectSemicolon(Subclause("23.2.2"));

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "expected ';', got 'module'",
                            1, "23.2.2"));
}

}  // namespace
}  // namespace delta
