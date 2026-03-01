// §14.12: Default clocking

#include "fixture_parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult15 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult15 Parse(const std::string& src) {
  ParseResult15 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =============================================================================
// LRM section 14.12 -- Default clocking
// =============================================================================
// §14.12: default clocking with negedge (variation of the LRM examples).
TEST(ParserSection14, DefaultClockingNegedge) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(negedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
}

// §14.12: default clocking block with end label.
TEST(ParserSection14, DefaultClockingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  default clocking bus @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : bus\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
}

// §14.12: unnamed default clocking block with multiple signals.
TEST(ParserSection14, DefaultClockingUnnamedMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input a, b;\n"
      "    output c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_signals.size(), 3u);
}

// =============================================================================
// A.6.11 clocking_declaration — default clocking reference form
// =============================================================================
TEST(ParserA611, DefaultClockingReference) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// default clocking as module_or_generate_item_declaration.
TEST(SourceText, DefaultClockingAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kClockingBlock);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->is_default_clocking);
}

struct ParseResult19 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult19 Parse(const std::string& src) {
  ParseResult19 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FindClockingBlock(ParseResult19& r, size_t idx = 0) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (count == idx) return item;
    ++count;
  }
  return nullptr;
}

// Validates parse result and retrieves a clocking block via output param.
// Must be called through ASSERT_NO_FATAL_FAILURE.
static void GetClockingBlock(ParseResult19& r, ModuleItem*& out,
                             size_t idx = 0) {
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  out = FindClockingBlock(r, idx);
  ASSERT_NE(out, nullptr);
}

// =============================================================================
// LRM section 19.5.1 -- Default clocking
// =============================================================================
// Declaring a clocking block inline as default.
TEST(ParserSection19, DefaultClocking_InlineDecl) {
  auto r = Parse(
      "module t;\n"
      "  default clocking bus @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
}

// Unnamed default clocking block.
TEST(ParserSection19, DefaultClocking_Unnamed) {
  auto r = Parse(
      "module t;\n"
      "  default clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

// Assigning an existing clocking block as default via a separate statement.
TEST(ParserSection19, DefaultClocking_SeparateStatement) {
  auto r = Parse(
      "module t;\n"
      "  clocking busA @(posedge clk1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking busA;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // The reference form creates a second clocking block item.
  auto& items = r.cu->modules[0]->items;
  bool found_ref = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking && item->clocking_event.empty()) {
      EXPECT_EQ(item->name, "busA");
      found_ref = true;
    }
  }
  EXPECT_TRUE(found_ref);
}

static ModuleItem* FindClockingBlock(ParseResult& r, size_t idx = 0) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (count == idx) return item;
    ++count;
  }
  return nullptr;
}

// =============================================================================
// A.6.11 clocking_declaration — default clocking
// =============================================================================
TEST(ParserA611, ClockingDeclDefault) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  EXPECT_EQ(item->name, "cb");
}

// =============================================================================
// A.6.11 clocking_declaration — unnamed default clocking
// =============================================================================
TEST(ParserA611, ClockingDeclUnnamed) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

}  // namespace
