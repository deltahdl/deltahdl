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

// =============================================================================
// A.8.4 Primaries — time_literal and time_unit
// =============================================================================
// § time_literal — unsigned_number time_unit (ns)
TEST(ParserA84, TimeLiteralNs) {
  auto r = Parse("module m; initial #5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserCh508, TimeLiteral_Ms) {
  EXPECT_TRUE(ParseOk("module m; initial #1ms; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Fs) {
  EXPECT_TRUE(ParseOk("module m; initial #500fs; endmodule"));
}

// § time_literal — unsigned_number time_unit (us)
TEST(ParserA84, TimeLiteralUs) {
  auto r = Parse("module m; initial #1us; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (ms)
TEST(ParserA84, TimeLiteralMs) {
  auto r = Parse("module m; initial #2ms; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (s)
TEST(ParserA84, TimeLiteralS) {
  auto r = Parse("module m; initial #1s; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Time literal variants in delay: fs, ps, ns, us, ms, s.
TEST(ParserA223, DelayValueAllTimeLiterals) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire #1fs w1;\n"
              "  wire #2ps w2;\n"
              "  wire #3ns w3;\n"
              "  wire #4us w4;\n"
              "  wire #5ms w5;\n"
              "  wire #6s w6;\n"
              "endmodule"));
}

// § time_literal — unsigned_number time_unit (ps)
TEST(ParserA84, TimeLiteralPs) {
  auto r = Parse("module m; initial #100ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (fs)
TEST(ParserA84, TimeLiteralFs) {
  auto r = Parse("module m; initial #50fs; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — fixed_point_number time_unit
TEST(ParserA84, TimeLiteralFixedPoint) {
  auto r = Parse("module m; initial #1.5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
