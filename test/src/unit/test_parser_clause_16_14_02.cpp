// §16.14.2: Assume statement

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
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #4: assume_property_statement
// =============================================================================
TEST(ParserA210, AssumeProperty_WithElseAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req)\n"
      "    $display(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

// assume_property_statement with no action block
TEST(ParserA210, AssumeProperty_NoActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

}  // namespace
