// Non-LRM tests

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
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

namespace {


// =============================================================================
// Section 8.23 -- Type-reference operator
// =============================================================================
// var type(expr) declaration.
TEST(ParserSection8, TypeRefVarDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real a = 1.0;\n"
              "  real b = 2.0;\n"
              "  var type(a + b) c;\n"
              "endmodule\n"));
}

// type(data_type) in parameter default.
TEST(ParserSection8, TypeRefDataTypeParam) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = type(logic [11:0]));\n"
              "endmodule\n"));
}

// type() comparison in expressions.
TEST(ParserSection8, TypeRefComparison) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) == type(int)) $display(\"int\");\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// Section 8.25 -- Enums
// =============================================================================
// Anonymous enum variable declaration with member inspection.
TEST(ParserSection8, EnumAnonymousDeclMembers) {
  auto r = Parse(
      "module m;\n"
      "  enum {IDLE, RUNNING, DONE} state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->name, "state");
  ASSERT_EQ(item->data_type.enum_members.size(), 3u);
  EXPECT_EQ(item->data_type.enum_members[0].name, "IDLE");
  EXPECT_EQ(item->data_type.enum_members[1].name, "RUNNING");
  EXPECT_EQ(item->data_type.enum_members[2].name, "DONE");
}

// Enum with explicit base type and value assignments.
TEST(ParserSection8, EnumExplicitBaseTypeValues) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  enum bit [3:0] {BRONZE = 4'h3, SILVER, GOLD = 4'h5}"
              " medal;\n"
              "endmodule\n"));
}

// Typedef enum used as a named type for variable declarations.
TEST(ParserSection8, EnumTypedefUsage) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {NO, YES} boolean;\n"
      "  boolean flag;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->name, "boolean");
  EXPECT_EQ(items[0]->typedef_type.enum_members.size(), 2u);
  EXPECT_EQ(items[1]->name, "flag");
}

// Class implementing multiple interface classes.
TEST(ParserSection8, ClassImplementsMultipleInterfaces) {
  EXPECT_TRUE(
      ParseOk("interface class A;\n"
              "  pure virtual function void fa();\n"
              "endclass\n"
              "interface class B;\n"
              "  pure virtual function void fb();\n"
              "endclass\n"
              "class C implements A, B;\n"
              "  virtual function void fa();\n"
              "  endfunction\n"
              "  virtual function void fb();\n"
              "  endfunction\n"
              "endclass\n"));
}

// Forward typedef class followed by full class definition.
TEST(ParserSection8, ForwardTypedefClassSelfRef) {
  auto r = Parse(
      "typedef class Node;\n"
      "class Node;\n"
      "  Node next;\n"
      "  int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Node");
}

TEST(Parser, ModuleWithInitialBlock) {
  auto r = Parse(
      "module hello;\n"
      "  initial $display(\"Hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST(Parser, AlwaysFFBlock) {
  auto r = Parse(
      "module counter(input logic clk, rst);\n"
      "  logic [7:0] count;\n"
      "  always_ff @(posedge clk or posedge rst)\n"
      "    if (rst) count <= '0;\n"
      "    else count <= count + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_ff = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock &&
        item->always_kind == AlwaysKind::kAlwaysFF) {
      found_ff = true;
    }
  }
  EXPECT_TRUE(found_ff);
}

// =============================================================================
// Parse-level fixture
// =============================================================================
struct ProgramTestParse : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// Elaboration fixture
// =============================================================================
struct ProgramElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

// =============================================================================
// §24.12 Program with final block
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithFinalBlock) {
  auto* unit = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
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

static void VerifyBlockVarDecls(const Stmt* blk,
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
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  auto* blk = item->body;
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

TEST(ParserCh90301, BlockVarDecl_WithInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* blk = r.cu->modules[0]->items[0]->body;
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
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->label, "block_a");
  EXPECT_EQ(body->stmts[1]->label, "block_b");
}

// §A.2.8 block_item_declaration alternative 3: parameter_declaration
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

// Mixed block items: all 4 alternatives together
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

// Nested blocks with declarations
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

// 5. Fork-join block creating a subscope
TEST(ParserClause03, Cl3_13_ForkJoinBlockSubscope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    fork\n"
              "      $display(\"a\");\n"
              "      $display(\"b\");\n"
              "    join\n"
              "  end\n"
              "endmodule\n"));
}

// 24. Named fork-join blocks
TEST(ParserClause03, Cl3_13_NamedForkJoinBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      $display(\"a\");\n"
      "      $display(\"b\");\n"
      "    join : my_fork\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto* fork_stmt = item->body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->label, "my_fork");
}

// block_item_declaration in fork/join (§9.3.2)
TEST(ParserA28, BlockItemInForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    int x;\n"
      "    x = 5;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  ASSERT_GE(body->fork_stmts.size(), 1u);
  EXPECT_EQ(body->fork_stmts[0]->kind, StmtKind::kVarDecl);
}

// typedef in fork/join
TEST(ParserA28, TypedefInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    typedef int my_t;\n"
              "  join\n"
              "endmodule\n"));
}

// Named block with declarations
TEST(ParserA28, NamedBlockWithDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    parameter int N = 4;\n"
      "    int i;\n"
      "    for (i = 0; i < N; i++) begin\n"
      "    end\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "my_block");
}

TEST(Parser, EventWaitWithParens) {
  auto r = Parse(
      "module t;\n"
      "  event ev;\n"
      "  initial @(ev) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[1];
  auto* stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

TEST(Parser, EventWaitBareIdentifier) {
  auto r = Parse(
      "module t;\n"
      "  event ev;\n"
      "  initial @ev ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[1];
  auto* stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

TEST(Parser, WaitStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    wait (ready) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(Parser, DisableStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    disable blk;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

static ModuleItem* FirstAlwaysItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.2.1 -- Initial and final blocks
// =============================================================================
TEST(ParserSection9, InitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection9, FinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// LRM section 9.2.2 -- Always blocks (always, always_comb, always_ff,
// always_latch)
// =============================================================================
TEST(ParserSection9, AlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_FALSE(item->sensitivity.empty());
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserSection9, AlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_FALSE(item->sensitivity.empty());
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
}

// =============================================================================
// LRM section 9.4.1 -- Delay control (#)
// =============================================================================
TEST(ParserSection9, DelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// =============================================================================
// LRM section 9.4.2 -- Event control (@)
// =============================================================================
TEST(ParserSection9, EventControlPosedgeKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection9, EventControlPosedgeEdge) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, EventControlNegedge) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

TEST(ParserSection9, EventControlMultiple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk or negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_GE(stmt->events.size(), 2u);
  const Edge kExpectedEdges[] = {Edge::kPosedge, Edge::kNegedge};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(stmt->events[i].edge, kExpectedEdges[i]);
  }
}

TEST(ParserSection9, EventControlComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_GE(stmt->events.size(), 2u);
}

// =============================================================================
// LRM section 9.4.2.2 -- @* and @(*) implicit event list
// =============================================================================
TEST(ParserSection9, StarEventBareAlways) {
  // always @* consumes the @* at the always-block level; body is the stmt.
  auto r = Parse(
      "module m;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, StarEventParenAlways) {
  // always @(*) consumes the @(*) at the always-block level.
  auto r = Parse(
      "module m;\n"
      "  always @(*) begin a = b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

TEST(ParserSection9, StarEventBareStmt) {
  // @* at the statement level produces an kEventControl stmt.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ParserSection9, StarEventParenStmt) {
  // @(*) at the statement level produces an kEventControl stmt.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// =============================================================================
// LRM section 9.4.2 -- iff guards on event expressions
// =============================================================================
TEST(ParserSection9, IffGuardPosedgeEdge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  // iff guard goes through always-block sensitivity path.
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, IffGuardPosedgeFields) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].signal, nullptr);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9, IffGuardNoEdge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, en, a, b;\n"
      "  always @(clk iff en) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kNone);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9, IffGuardMultipleEventsFirst) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0 or negedge reset) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9, IffGuardMultipleEventsSecond) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0 or negedge reset) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
}

TEST(ParserSection9, IffGuardStmtLevelKind) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  initial @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
}

TEST(ParserSection9, IffGuardStmtLevelEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  initial @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

TEST(ParserSection9, WaitExprStillWorks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserSection9, DisableIdentStillWorks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable my_block;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

// =============================================================================
// LRM section 9.4.5 -- repeat event control
// =============================================================================
TEST(ParserSection9, RepeatEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(3) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

}  // namespace
