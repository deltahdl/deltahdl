#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, CheckerEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleAndHierarchyParsing, EndLabelInterface) {
  auto r = Parse("interface myif; endinterface : myif\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "myif");
}

TEST(ModuleAndHierarchyParsing, EndLabelProgram) {
  auto r = Parse("program myprog; endprogram : myprog\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->name, "myprog");
}

// §3.1 — Error: mismatched end label.
TEST(BlockNames, MismatchedEndLabelIsError) {
  EXPECT_FALSE(ParseOk("module foo; endmodule : bar\n"));
}

TEST(BlockNameParsing, LabeledSeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

TEST(BlockNameParsing, LabeledSeqBlockWithMatchingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk\n"
      "    a = 1;\n"
      "  end : blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "blk");
}

TEST(BlockNameParsing, MismatchedEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : foo\n"
      "    a = 1;\n"
      "  end : bar\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, NamedForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : workers\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join : workers\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "workers");
}

TEST(BlockNameParsing, NamedForkMismatchedEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : alpha\n"
      "      a = 1;\n"
      "    join : beta\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, NamedForkWithJoinAnyLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : fg\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join_any : fg\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "fg");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockNameParsing, NamedForkWithJoinNoneLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : bg\n"
      "      a = 1;\n"
      "    join_none : bg\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "bg");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

TEST(BlockNameParsing, MismatchedJoinAnyEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : x\n"
      "      a = 1;\n"
      "    join_any : y\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, MismatchedJoinNoneEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : x\n"
      "      a = 1;\n"
      "    join_none : y\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, EndLabelOnUnnamedSeqBlockError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "  end : orphan\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, JoinLabelOnUnnamedForkError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    join : orphan\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, NamedBlockWithVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end : blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "blk");
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(BlockNameParsing, NestedNamedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "inner");
}

TEST(BlockNameParsing, NamedEmptySeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : empty_blk\n"
      "  end : empty_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "empty_blk");
  EXPECT_EQ(body->stmts.size(), 0u);
}

TEST(BlockNameParsing, NamedEmptyForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : empty_fork\n"
      "    join : empty_fork\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "empty_fork");
  EXPECT_EQ(stmt->fork_stmts.size(), 0u);
}

}  // namespace
