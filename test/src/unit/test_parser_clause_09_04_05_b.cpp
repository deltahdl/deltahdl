// §9.4.5: Intra-assignment timing controls

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// =============================================================================
// LRM section 9.4.5 -- Repeat event signal field populated
// =============================================================================
// Verify the signal field of the event expression.
TEST(ParserSection9, Sec9_4_5_RepeatEventSignalField) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(2) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  ASSERT_NE(stmt->events[0].signal, nullptr);
  EXPECT_EQ(stmt->events[0].signal->text, "clk");
}

// =============================================================================
// LRM section 9.4.5 -- ParseOk: repeat event parses without errors
// =============================================================================
// Validate ParseOk for a complete repeat event control scenario.
TEST(ParserSection9, Sec9_4_5_ParseOkRepeatEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg clk, a, b;\n"
              "  initial begin\n"
              "    a = repeat(10) @(posedge clk) b;\n"
              "    a <= repeat(5) @(negedge clk) b;\n"
              "  end\n"
              "endmodule\n"));
}

struct ParseResult9f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static Stmt* FirstInitialStmt(ParseResult9f& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

struct ParseResult9g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9g Parse(const std::string& src) {
  ParseResult9g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.4.5 -- Intra-assignment delay no events field set
// =============================================================================
// Intra-assignment delay should not set the events field.
TEST(ParserSection9, Sec9_4_5_IntraDelayNoEventsField) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a = #10 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_TRUE(stmt->events.empty());
  EXPECT_EQ(stmt->repeat_event_count, nullptr);
}

}  // namespace
