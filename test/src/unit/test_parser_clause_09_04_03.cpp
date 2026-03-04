// §9.4.3: Level-sensitive event control

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection9, WaitStatementWithBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (ready) begin\n"
                 "      a = 1;\n"
                 "      b = 2;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}
// ---------------------------------------------------------------------------
// 15. wait statement for level-sensitive control
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_WaitStatement) {
  auto r = Parse("module m;\n"
                 "  reg done, a;\n"
                 "  initial begin\n"
                 "    wait (done) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// --- Test helpers ---
// =============================================================================
// §15.5 — Wait on event
// =============================================================================
TEST(ParserSection15, WaitOnEvent) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait(done);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// =============================================================================
// §9.4.3 / §9.4.2.4 -- Wait statement
// =============================================================================
TEST(ParserSection9b, WaitStatementBasic) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (!enable) #10 a = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserSection9b, WaitStatementExpression) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (done == 1) $display(\"done\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
}

// §9.4.3: wait_statement
TEST(ParserA604, StmtItemWaitStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (done) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// ---------------------------------------------------------------------------
// wait_statement ::=
//   wait ( expression ) statement_or_null
//   | wait fork ;
//   | wait_order ( hierarchical_identifier { , hierarchical_identifier } )
//     action_block
// ---------------------------------------------------------------------------
// §9.4.3: wait (condition) statement
TEST(ParserA605, WaitConditionStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (ready) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// §9.4.3: wait (condition) null statement
TEST(ParserA605, WaitConditionNull) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (ready) ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}
TEST(Parser, WaitStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    wait (ready) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection9, WaitExprStillWorks) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (done) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

} // namespace
