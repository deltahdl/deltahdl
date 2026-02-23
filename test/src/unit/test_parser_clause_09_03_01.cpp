#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

// §9.3.1 Block-level variable declarations

using namespace delta;

struct ParseResult90301 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult90301 Parse(const std::string &src) {
  ParseResult90301 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
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

static void VerifyBlockVarDecls(const Stmt *blk,
                                const std::string expected_names[],
                                size_t count) {
  ASSERT_EQ(blk->stmts.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(blk->stmts[i]->kind, StmtKind::kVarDecl) << "stmt " << i;
    EXPECT_EQ(blk->stmts[i]->var_name, expected_names[i]) << "stmt " << i;
  }
}

TEST(ParserCh90301, BlockVarDecl_BuiltinType_Block) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  auto *blk = item->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->kind, StmtKind::kBlock);
  ASSERT_EQ(blk->stmts.size(), 1u);
}

TEST(ParserCh90301, BlockVarDecl_BuiltinType_Stmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(blk->stmts[0]->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(blk->stmts[0]->var_name, "x");
}

TEST(ParserCh90301, BlockVarDecl_UserDefinedType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a, b[4];} ab_t;\n"
              "  initial begin\n"
              "    ab_t v1[1:0] [2:0];\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserCh90301, BlockVarDecl_CommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a, b, c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  std::string expected_names[] = {"a", "b", "c"};
  VerifyBlockVarDecls(blk, expected_names, std::size(expected_names));
}

TEST(ParserCh90301, BlockVarDecl_WithInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_NE(blk->stmts[0]->var_init, nullptr);
}

TEST(ParserCh90301, BlockVarDecl_FullStructReplication) {
  EXPECT_TRUE(
      ParseOk("module top();\n"
              "  struct {int X,Y,Z;} XYZ = '{3{1}};\n"
              "  typedef struct {int a,b[4];} ab_t;\n"
              "  int a,b,c;\n"
              "  initial begin\n"
              "    ab_t v1[1:0] [2:0];\n"
              "    v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
              "  end\n"
              "endmodule\n"));
}
struct ParseResult313 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult313 Parse(const std::string &src) {
  ParseResult313 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool HasItemOfKindAndName(const std::vector<ModuleItem *> &items,
                                 ModuleItemKind kind, const std::string &name) {
  for (const auto *item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

static bool HasAttrNamed(const std::vector<ModuleItem *> &items,
                         const std::string &name) {
  for (const auto *item : items)
    for (const auto &attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

// 3. Named begin-end block creating a subscope
TEST(ParserClause03, Cl3_13_NamedBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    int x;\n"
      "    x = 1;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto *mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto *item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "my_block");
}

// 4. Nested named begin-end blocks
TEST(ParserClause03, Cl3_13_NestedNamedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      int y;\n"
      "      y = 42;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "outer");
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->label, "inner");
}

// 25. begin-end with no name (anonymous block)
TEST(ParserClause03, Cl3_13_AnonymousBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  // Anonymous blocks have an empty label.
  EXPECT_TRUE(item->body->label.empty());
}

// 26. Multiple named blocks at same level
TEST(ParserClause03, Cl3_13_MultipleNamedBlocksSameLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin : block_a\n"
      "      int x;\n"
      "      x = 1;\n"
      "    end : block_a\n"
      "    begin : block_b\n"
      "      int y;\n"
      "      y = 2;\n"
      "    end : block_b\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->label, "block_a");
  EXPECT_EQ(body->stmts[1]->label, "block_b");
}

