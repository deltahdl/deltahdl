// §7.10: Queues

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, VarDeclAssignmentQueueDim) {
  auto r = Parse("module m; int q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "q");
}

// ---------------------------------------------------------------------------
// variable_dimension ::= unsized_dimension | unpacked_dimension
//                       | associative_dimension | queue_dimension
// (This is a union production; each alternative is tested above/below.)
// ---------------------------------------------------------------------------
TEST(ParserA25, VarDimAllFourAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  int d [];       \n"
      "  int u [3:0];    \n"
      "  int a [string]; \n"
      "  int q [$];      \n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  // unsized_dimension: nullptr sentinel
  ASSERT_EQ(items[0]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[0]->unpacked_dims[0], nullptr);
  // unpacked_dimension: range
  ASSERT_EQ(items[1]->unpacked_dims.size(), 1u);
  ASSERT_NE(items[1]->unpacked_dims[0], nullptr);
  EXPECT_EQ(items[1]->unpacked_dims[0]->kind, ExprKind::kBinary);
  // associative_dimension: string type
  ASSERT_EQ(items[2]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[2]->unpacked_dims[0]->text, "string");
  // queue_dimension: $
  ASSERT_EQ(items[3]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[3]->unpacked_dims[0]->text, "$");
}

// ---------------------------------------------------------------------------
// queue_dimension ::= [ $ [ : constant_expression ] ]
// ---------------------------------------------------------------------------
TEST(ParserA25, QueueDimUnbounded) {
  auto r = Parse("module m; int q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  EXPECT_EQ(item->unpacked_dims[0]->rhs, nullptr);
}

struct ParseResult7b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ModuleItem* FirstItem(ParseResult7b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// --- Test helpers ---
struct ParseResult7c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7c Parse(const std::string& src) {
  ParseResult7c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =========================================================================
// §7.10: Queues (additional tests)
// =========================================================================
TEST(ParserSection7, QueueDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q");
}

TEST(ParserSection7, QueueWithInitializer) {
  auto r = Parse(
      "module t;\n"
      "  integer Q[$] = '{3, 2, 7};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Q");
  EXPECT_NE(item->init_expr, nullptr);
}

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7 Parse(const std::string& src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult7& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =========================================================================
// §7.10: Queues
// =========================================================================
TEST(ParserSection7, QueueUnbounded) {
  auto r = Parse(
      "module t;\n"
      "  byte q[$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// =========================================================================
// §7.7: Queues — additional declaration forms
// =========================================================================
TEST(ParserSection7, QueueOfStrings) {
  auto r = Parse(
      "module t;\n"
      "  string names[$] = '{\"Bob\"};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "names");
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
