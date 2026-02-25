// §16.14.3: Cover statement

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

TEST(ParserA210, ConcurrentAssertionItem_CoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

// =============================================================================
// §A.2.10 Production #7: cover_sequence_statement
// cover_sequence_statement ::=
//     cover sequence ( [clocking_event] [disable iff (expr)] sequence_expr )
//     statement_or_null
// =============================================================================
TEST(ParserA210, CoverSequence_Basic) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, CoverSequence_WithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##2 b ##1 c)\n"
      "    $display(\"seq covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
}

TEST(ParserA210, CoverSequence_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cover sequence (@(posedge clk) disable iff (rst) a ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CoverSequence_Kind) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kCoverSequence);
}

// =============================================================================
// §A.2.10 Production #5: cover_property_statement
// =============================================================================
TEST(ParserA210, CoverProperty_WithPassStmt) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
}

TEST(ParserA210, CoverSequence_HasAssertExpr) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

}  // namespace
