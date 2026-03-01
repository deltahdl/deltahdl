// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysLatchItem(ParseResult9i& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

namespace {

// ---------------------------------------------------------------------------
// 27. always_latch with deeply nested if-else-if chain.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_DeepIfElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d, q;\n"
      "  always_latch\n"
      "    if (a)\n"
      "      q <= 4'h1;\n"
      "    else if (b)\n"
      "      q <= 4'h2;\n"
      "    else if (c)\n"
      "      q <= 4'h3;\n"
      "    else\n"
      "      q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  auto* top_if = item->body;
  ASSERT_NE(top_if, nullptr);
  EXPECT_EQ(top_if->kind, StmtKind::kIf);
  // First else branch is an if.
  ASSERT_NE(top_if->else_branch, nullptr);
  EXPECT_EQ(top_if->else_branch->kind, StmtKind::kIf);
  // Second else branch is also an if.
  auto* mid_if = top_if->else_branch;
  ASSERT_NE(mid_if->else_branch, nullptr);
  EXPECT_EQ(mid_if->else_branch->kind, StmtKind::kIf);
  // Terminal else is a plain assignment.
  auto* inner_if = mid_if->else_branch;
  ASSERT_NE(inner_if->else_branch, nullptr);
  EXPECT_EQ(inner_if->else_branch->kind, StmtKind::kNonblockingAssign);
}

// ---------------------------------------------------------------------------
// 28. always_latch with system function call in body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_SystemFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic en;\n"
              "  logic [7:0] q, d;\n"
              "  always_latch begin\n"
              "    if (en) begin\n"
              "      q <= d;\n"
              "      $display(\"latch update\");\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 29. Case with begin-end blocks in items inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_CaseWithBeginEndItems) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] q, a, b;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: begin\n"
      "        q <= a;\n"
      "      end\n"
      "      2'b01: begin\n"
      "        q <= b;\n"
      "      end\n"
      "      default: begin\n"
      "        q <= q;\n"
      "      end\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  ASSERT_GE(item->body->case_items.size(), 3u);
  for (const auto& ci : item->body->case_items) {
    ASSERT_NE(ci.body, nullptr);
    EXPECT_EQ(ci.body->kind, StmtKind::kBlock);
  }
}

}  // namespace
