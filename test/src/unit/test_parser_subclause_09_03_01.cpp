#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(SequentialBlockParsing, StatementsWithDelaysAndEventControl) {
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

TEST(SequentialBlockParsing, SequentialBlockMultipleLocalVars) {
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

TEST(SequentialBlockParsing, BlockWithSystemCalls) {
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

TEST(SequentialBlockParsing, BlockWithMixedBlockingNonblocking) {
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

TEST(BlockVarDeclParsing, BuiltinTypeDecl) {
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

TEST(BlockVarDeclParsing, UserDefinedTypeDecl) {
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

TEST(BlockVarDeclParsing, CommaSeparatedDecls) {
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

TEST(SequentialBlockParsing, LocalVarDecl) {
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

TEST(BlockItemDeclParsing, NestedBlocksWithDecls) {
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

TEST(SequentialBlockParsing, SeqBlockAsStatement) {
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

TEST(SequentialBlockParsing, SeqBlockGroupsAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->then_branch->stmts.size(), 2u);
}

TEST(SequentialBlockParsing, EmptySeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->stmts.size(), 0u);
}

// Syntax 9-2 gives seq_block an optional [ : block_identifier ] after begin.
// Exercise that BNF element: a named begin-end block parses and the block
// identifier is recorded on the block statement.
TEST(SequentialBlockParsing, NamedSequentialBlockRecordsBlockIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin : blk\n"
      "      a = 1;\n"
      "    end : blk\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->label, "blk");
}

TEST(SequentialBlockParsing, NullStatementInSeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ;\n"
      "    a = 1;\n"
      "    ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequentialBlockParsing, MissingEndKeywordProducesParseError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "endmodule\n");
  // The block's statement loop stops at `endmodule` without consuming it, so
  // ParseBlockStmt asks for `end` at that token, on line 4. It asked at the EOF
  // on line 5 until the loop was given the stop set, the block having swallowed
  // the `endmodule` looking for a statement.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endmodule'", 4, "9.3.1"));
}

TEST(BlockItemDeclParsing, LocalParamAsBlockItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    localparam P = 1;\n"
      "    a = P;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "P");
}

TEST(BlockItemDeclParsing, ParameterAsBlockItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    parameter Q = 2;\n"
      "    a = Q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "Q");
}

TEST(BlockItemDeclParsing, LetDeclAsBlockItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    let inc(a) = a + 1;\n"
      "    x = inc(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockItemDecl);
}

TEST(BlockItemDeclParsing, AttributeInstanceBeforeBlockItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* foo *) int x;\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  ASSERT_EQ(body->stmts[0]->attrs.size(), 1u);
  EXPECT_EQ(body->stmts[0]->attrs[0].name, "foo");
}

// §9.3.1 is what makes the `end` obligatory: a sequential block is "delimited
// by the keywords begin and end", so a source that runs out before the closing
// keyword breaches that subclause and no other. The sentence Parser::Expect
// writes names the token it wanted rather than the rule, so the subclause on
// the record is the only thing that says which rule was read. The block's
// report comes first because the block is what the parser is inside when the
// source runs out; the module's own missing `endmodule` is reported after it.
TEST(SequentialBlockParsing, MissingEndNames9_3_1) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'end'", 3, "9.3.1"));
}

// A.2.2.1 lets a data_type be a type_identifier behind a package_scope, and
// A.2.8 lets any data_declaration open a sequential block, so `pkg::t v;` is a
// block item whatever the enclosing scope has imported. The package's type is
// never imported here and `pkg` is a package name rather than a type name, so
// the declaration is decided on the `::` alone: a predicate that first asked
// whether the leading name is a known type read the line as an expression
// statement and demanded a `;` where the variable name stands.
static const char* const kScopedTypePackage =
    "package pkg;\n"
    "  typedef logic [3:0] nib_t;\n"
    "  function automatic int f(int x); return x; endfunction\n"
    "  task automatic t(); endtask\n"
    "  int v;\n"
    "  int arr[4];\n"
    "endpackage\n";

static void ExpectScopedNibDecl(const Stmt* s, std::string_view var_name) {
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kVarDecl);
  EXPECT_EQ(s->var_decl_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(s->var_decl_type.scope_name, "pkg");
  EXPECT_EQ(s->var_decl_type.type_name, "nib_t");
  EXPECT_EQ(s->var_name, var_name);
}

TEST(BlockVarDeclParsing, PackageScopedTypeDeclInSeqBlock) {
  auto r = Parse(std::string(kScopedTypePackage) +
                 "module m;\n"
                 "  initial begin\n"
                 "    pkg::nib_t v;\n"
                 "    v = 4'd3;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  ExpectScopedNibDecl(body->stmts[0], "v");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
}

// The packed dimension A.2.2.1 lets follow the type_identifier: `[` after the
// scoped name is not what makes the line a statement, the token after the
// closing `]` is.
TEST(BlockVarDeclParsing, PackageScopedTypeWithPackedDimDeclInSeqBlock) {
  auto r = Parse(std::string(kScopedTypePackage) +
                 "module m;\n"
                 "  initial begin\n"
                 "    pkg::nib_t [1:0] w;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  ExpectScopedNibDecl(body->stmts[0], "w");
  EXPECT_NE(body->stmts[0]->var_decl_type.packed_dim_left, nullptr);
}

TEST(BlockVarDeclParsing, PackageScopedTypeDeclInForkBlock) {
  auto r = Parse(std::string(kScopedTypePackage) +
                 "module m;\n"
                 "  initial\n"
                 "    fork\n"
                 "      pkg::nib_t v;\n"
                 "      v = 4'd3;\n"
                 "    join\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  ASSERT_EQ(body->fork_stmts.size(), 2u);
  ExpectScopedNibDecl(body->fork_stmts[0], "v");
  EXPECT_EQ(body->fork_stmts[1]->kind, StmtKind::kBlockingAssign);
}

TEST(BlockVarDeclParsing, PackageScopedTypeDeclInFunctionBody) {
  auto r = Parse(std::string(kScopedTypePackage) +
                 "module m;\n"
                 "  function automatic int g();\n"
                 "    pkg::nib_t v;\n"
                 "    v = 4'd3;\n"
                 "    return v;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FindFunc(r, "g");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_body_stmts.size(), 3u);
  ExpectScopedNibDecl(fn->func_body_stmts[0], "v");
  EXPECT_EQ(fn->func_body_stmts[1]->kind, StmtKind::kBlockingAssign);
}

// The same leading `pkg::` opens a statement when what follows the scoped name
// is a call's `(`, an assignment operator, a select on the way to one, or the
// `;` of a task call written without its argument list, so each of these stays
// the statement it is with the leading name unknown as a type. `pkg::arr[0]`
// is what tells the packed-dimension case above apart: after the `]` comes `=`
// here and a variable name there.
TEST(BlockVarDeclParsing, PackageScopedCallAndAssignStayStatements) {
  auto r = Parse(std::string(kScopedTypePackage) +
                 "module m;\n"
                 "  initial begin\n"
                 "    pkg::f(1);\n"
                 "    pkg::v = 1;\n"
                 "    pkg::v <= 2;\n"
                 "    pkg::v += 3;\n"
                 "    pkg::arr[0] = 4;\n"
                 "    pkg::v++;\n"
                 "    pkg::t;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 7u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(body->stmts[6]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[3]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[4]->kind, StmtKind::kBlockingAssign);
  for (const Stmt* s : body->stmts) EXPECT_NE(s->kind, StmtKind::kVarDecl);
}

}  // namespace
