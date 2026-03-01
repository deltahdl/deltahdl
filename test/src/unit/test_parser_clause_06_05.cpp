// §6.5: for more details.

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =========================================================================
// §6.5: Nets and variables
// =========================================================================
TEST(ParserSection6, NetsCantBeProcAssigned) {
  // Nets are driven by continuous assignments, variables by procedural.
  // This test verifies both constructs parse correctly.
  auto r = Parse(
      "module t;\n"
      "  wire a;\n"
      "  assign a = 1'b1;\n"
      "  logic b;\n"
      "  initial b = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 4u);
}

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string& src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// 13. Variable driven by initial block (procedural assignment).
TEST(ParserSection6, Sec6_5_VarDrivenByInitialBlock) {
  auto r = Parse(
      "module t;\n"
      "  logic q;\n"
      "  initial q = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(items[1]->body, nullptr);
}

// 26. Mixed net and variable declarations coexist in same module.
TEST(ParserSection6, Sec6_5_MixedNetAndVarDecls) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] net_a;\n"
      "  logic [7:0] var_b;\n"
      "  tri net_c;\n"
      "  int var_d;\n"
      "  reg var_e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 5u);
  // Nets
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[2]->data_type.is_net);
  // Variables
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[1]->data_type.is_net);
  EXPECT_EQ(items[3]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[3]->data_type.is_net);
  EXPECT_EQ(items[4]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[4]->data_type.is_net);
}

}  // namespace
