// §16.14.4: Restrict statement

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

// =============================================================================
// §A.2.10 Production #8: restrict_property_statement
// restrict_property_statement ::= restrict property ( property_spec ) ;
// =============================================================================
TEST(ParserA210, RestrictProperty_Basic) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, RestrictProperty_Kind) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) req |-> ##[1:3] ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kRestrictProperty);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(ParserA210, RestrictProperty_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  restrict property (\n"
              "    @(posedge clk) disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, RestrictProperty_HasAssertExpr) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

}  // namespace
