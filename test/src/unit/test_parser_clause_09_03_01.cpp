#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(ParserA28, ParameterInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    parameter int Y = 10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_name, "Y");
}

TEST(ParserA28, MixedBlockItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    parameter int P = 1;\n"
              "    localparam int LP = 2;\n"
              "    int x = 3;\n"
              "    x = x + P + LP;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, NestedBlocksWithDecls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    int x = 1;\n"
              "    begin\n"
              "      int y = 2;\n"
              "      x = x + y;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}
static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

TEST(ParserSection9, Sec9_2_3_VarDeclInBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] q, d;\n"
      "  always_latch begin\n"
      "    logic [7:0] tmp;\n"
      "    tmp = d + 1;\n"
      "    if (en) q <= tmp;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ParserSection9, Sec9_3_1_EmptyBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_TRUE(body->stmts.empty());
}

TEST(ParserSection9, Sec9_3_1_SingleStatementInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_MultipleAssignmentsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    c = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

TEST(ParserA604, StmtItemSeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
}

TEST(ParserA28, ImportInBlock) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  int x = 5;\n"
              "endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    import pkg::*;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9, Sec9_3_1_VarDeclAsFirstStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int temp;\n"
      "    temp = 99;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "temp");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_MultipleDifferentTypeVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    logic [7:0] y;\n"
      "    real z;\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[3]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_VarDeclWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int count = 10;\n"
      "    $display(\"%0d\", count);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "count");
  EXPECT_NE(body->stmts[0]->var_init, nullptr);
}

TEST(ParserSection9, Sec9_3_1_NestedBeginEndTwoLevels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    begin\n"
      "      b = 1;\n"
      "      c = 2;\n"
      "    end\n"
      "    d = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_DeeplyNestedBeginEndThreeLevels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      begin\n"
      "        a = 1;\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  auto* mid = body->stmts[0];
  EXPECT_EQ(mid->kind, StmtKind::kBlock);
  ASSERT_EQ(mid->stmts.size(), 1u);
  auto* inner = mid->stmts[0];
  EXPECT_EQ(inner->kind, StmtKind::kBlock);
  ASSERT_EQ(inner->stmts.size(), 1u);
  EXPECT_EQ(inner->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_NamedNestedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : mid\n"
      "      begin : inner\n"
      "        x = 1;\n"
      "      end : inner\n"
      "    end : mid\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->label, "mid");
  ASSERT_EQ(body->stmts[0]->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->stmts[0]->label, "inner");
}

TEST(ParserSection6, BlockLevelParameter) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    parameter int P = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection6, BlockLevelLocalparam) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    localparam int LP = 10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}
