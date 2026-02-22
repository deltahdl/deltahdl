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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  typedef struct {int a, b[4];} ab_t;\n"
                      "  initial begin\n"
                      "    ab_t v1[1:0] [2:0];\n"
                      "  end\n"
                      "endmodule\n"));
}

TEST(ParserCh90301, BlockVarDecl_CommaSeparated) {
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  EXPECT_TRUE(ParseOk("module top();\n"
                      "  struct {int X,Y,Z;} XYZ = '{3{1}};\n"
                      "  typedef struct {int a,b[4];} ab_t;\n"
                      "  int a,b,c;\n"
                      "  initial begin\n"
                      "    ab_t v1[1:0] [2:0];\n"
                      "    v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
                      "  end\n"
                      "endmodule\n"));
}
