// §9.3.1: Sequential blocks

#include "fixture_parser.h"

using namespace delta;

namespace {

// attribute_instance prefix on block items
TEST(ParserA28, AttrOnDataDeclInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) int x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, AttrOnLocalparamInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) localparam int X = 5;\n"
              "  end\n"
              "endmodule\n"));
}

// §A.2.8 block_item_declaration alternative 1: data_declaration
// data_declaration ::= [ const ] [ var ] [ lifetime ] data_type_or_implicit
//                      list_of_variable_decl_assignments ;
TEST(ParserA28, DataDeclBasicInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "x");
}

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

// Helpers to extract items from the first module.
static ModuleItem* FindItem(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

TEST(ParserA602, InitialConstruct_BeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

TEST(ParserA602, AlwaysConstruct_WithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) begin\n"
      "    q <= d;\n"
      "    r <= e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserA602, Integration_InitialWithTimingAndAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    @(posedge done) $finish;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kEventControl);
}

static Stmt* InitialBody(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    return item->body;
  }
  return nullptr;
}

// =============================================================================
// A.6.3 Parallel and sequential blocks
// =============================================================================
// ---------------------------------------------------------------------------
// seq_block: begin...end
// ---------------------------------------------------------------------------
// §9.3.1: Basic sequential block
TEST(ParserA603, SeqBlockBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts.size(), 2u);
}

// §9.3.1: Empty sequential block
TEST(ParserA603, SeqBlockEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts.size(), 0u);
}

// §A.2.8: Sequential block with block_item_declaration (variable)
TEST(ParserA603, SeqBlockWithVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

// §9.3.1: Nested sequential blocks
TEST(ParserA603, SeqBlockNested) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 1;\n"
      "    end\n"
      "    begin\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
}

// §A.2.8: Sequential block with parameter declaration
TEST(ParserA603, SeqBlockWithParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    parameter int P = 42;\n"
      "    a = P;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_GE(body->stmts.size(), 2u);
}

struct ParseResult9d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9d Parse(const std::string& src) {
  ParseResult9d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks
// Block-level variable declarations (block_item_declaration).
// =============================================================================
TEST(ParserSection9c, SequentialBlockWithLocalVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "    $display(\"%0d\", x);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ParserSection9c, SequentialBlockMultipleLocalVars) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a;\n"
      "    int b;\n"
      "    a = 1;\n"
      "    b = a + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
}

struct ParseResult9e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9e Parse(const std::string& src) {
  ParseResult9e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with system function calls.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithSystemCalls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "    $write(\"world\");\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kExprStmt);
}

TEST(ParserSection9, Sec9_3_1_BlockWithMixedBlockingNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    temp = a + b;\n"
      "    result <= temp;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

struct ParseResult90301 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult90301 Parse(const std::string& src) {
  ParseResult90301 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

TEST(ParserCh90301, BlockVarDecl_BuiltinType_Block) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  auto* blk = item->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->kind, StmtKind::kBlock);
  ASSERT_EQ(blk->stmts.size(), 1u);
}

TEST(ParserSection9, Sec9_3_1_StaticVarDeclInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int call_count = 0;\n"
      "    call_count = call_count + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_static);
  EXPECT_FALSE(body->stmts[0]->var_is_automatic);
  EXPECT_EQ(body->stmts[0]->var_name, "call_count");
}

TEST(ParserCh90301, BlockVarDecl_BuiltinType_Stmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* blk = r.cu->modules[0]->items[0]->body;
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

static void VerifyBlockVarDecls(const Stmt* blk,
                                const std::string expected_names[],
                                size_t count) {
  ASSERT_EQ(blk->stmts.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(blk->stmts[i]->kind, StmtKind::kVarDecl) << "stmt " << i;
    EXPECT_EQ(blk->stmts[i]->var_name, expected_names[i]) << "stmt " << i;
  }
}

TEST(ParserCh90301, BlockVarDecl_CommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a, b, c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  std::string expected_names[] = {"a", "b", "c"};
  VerifyBlockVarDecls(blk, expected_names, std::size(expected_names));
}

// =============================================================================
// LRM section 9.3.1 -- Block with only variable declarations (no statements).
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithOnlyVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a;\n"
      "    logic [3:0] b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
}

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection9, SequentialBlockVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int temp;\n"
      "    temp = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

// =============================================================================
// LRM section 9.3.1 -- ParseOk smoke tests for complex block scenarios.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_MultipleSequentialBlocksInSameInitial) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin : first\n"
      "      a = 1;\n"
      "    end : first\n"
      "    begin : second\n"
      "      b = 2;\n"
      "    end : second\n"
      "    begin : third\n"
      "      c = 3;\n"
      "    end : third\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "first");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->label, "second");
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[2]->label, "third");
}

TEST(ParserSection9, SequentialBlockNestedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 1;\n"
      "    end\n"
      "    begin\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
}

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 21. always_comb with local variable declaration
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_LocalVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, result;\n"
      "  always_comb begin\n"
      "    logic [8:0] temp;\n"
      "    temp = a + b;\n"
      "    result = temp[7:0];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, SequentialBlockMultipleVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; logic [7:0] y; x = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
}

}  // namespace
