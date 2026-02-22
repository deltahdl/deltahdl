// §10.3: Continuous assignments

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace delta;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind)
      return item;
  }
  return nullptr;
}

namespace {

TEST(Lexical, ContAssign_WithDelay) {
  auto r = Parse("module top;\n"
                 "  wire out, in;\n"
                 "  assign #5 out = in;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  const auto *assign_item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign);
  ASSERT_NE(assign_item, nullptr) << "no continuous assignment found";
  ASSERT_NE(assign_item->assign_delay, nullptr);
  EXPECT_EQ(assign_item->assign_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(assign_item->assign_delay->int_val, 5);
}

TEST(Lexical, ContAssign_WithParenDelay) {
  auto r = Parse("module top;\n"
                 "  wire out, in;\n"
                 "  assign #(10) out = in;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign)
      continue;
    found = true;
    ASSERT_NE(item->assign_delay, nullptr);
    EXPECT_EQ(item->assign_delay->int_val, 10);
  }
  EXPECT_TRUE(found);
}

TEST(Lexical, ContAssign_NoDelay) {
  auto r = Parse("module top;\n"
                 "  wire a, b;\n"
                 "  assign a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign)
      continue;
    EXPECT_EQ(item->assign_delay, nullptr);
  }
}

} // namespace
