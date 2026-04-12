#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(LevelSensitiveEventParsing, WaitStatementWithBlock) {
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

TEST(LevelSensitiveEventParsing, WaitNullBody) {
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

TEST(LevelSensitiveEventParsing, WaitNegatedCondition) {
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

TEST(LevelSensitiveEventParsing, WaitComparisonCondition) {
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


TEST(LevelSensitiveEventParsing, WaitWithAssignment) {
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

TEST(LevelSensitiveEventParsing, WaitConditionNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (ready) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

TEST(LevelSensitiveEventParsing, WaitMissingLParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial wait ready a = 1;\n"
      "endmodule\n").has_errors);
}

TEST(LevelSensitiveEventParsing, WaitMissingRParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial wait(ready a = 1;\n"
      "endmodule\n").has_errors);
}

}  // namespace
