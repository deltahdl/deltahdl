#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProcessParsing, WaitStatementWithBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (ready) begin\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(SchedulingSemanticsParsing, WaitStatement) {
  auto r = Parse(
      "module m;\n"
      "  reg done, a;\n"
      "  initial begin\n"
      "    wait (done) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(InterprocessSyncParsing, WaitOnEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait(done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ProceduralAssignAndControlParsing, WaitStatementBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ProceduralAssignAndControlParsing, WaitStatementExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done == 1) $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
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

TEST(ProcessParsing, WaitExprStillWorks) {
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

}  // namespace
