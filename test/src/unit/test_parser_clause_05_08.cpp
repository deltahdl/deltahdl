// §5.8: Time literals

#include "fixture_parser.h"

using namespace delta;

// --- §5.12 Attributes ---
struct ParseResult512 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult512 Parse(const std::string& src) {
  ParseResult512 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult512& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

namespace {

TEST(ParserCh508, TimeLiteral_IntegerNs) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

// § primary_literal — time_literal
TEST(ParserA84, PrimaryLiteralTimeLiteral) {
  auto r = Parse("module m; initial #10ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserCh508, TimeLiteral_FixedPointNs) {
  // 2.1ns -- a time literal with a fixed-point value.
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Ps) {
  EXPECT_TRUE(ParseOk("module m; initial #40ps; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Us) {
  EXPECT_TRUE(ParseOk("module m; initial #100us; endmodule"));
}

}  // namespace
