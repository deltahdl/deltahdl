#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingControlSyntaxParsing, ProceduralTimingControlDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlockingAssign);
}

TEST(TimingControlSyntaxParsing, ProceduralTimingControlDelayNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

// Tests of @(posedge clk) and @(posedge clk) ; — covering §9.4.2's event
// control with body and null body — were moved to
// test_parser_clause_09_04_02.cpp as §9.4.2 owns those rules.

TEST(TimingControlSyntaxParsing, ProceduralTimingControlDelayBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// @(posedge clk) begin ... end was moved to test_parser_clause_09_04_02.cpp.

TEST(TimingControlSyntaxParsing, NestedDelayWrappingEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #5 @(posedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->kind, StmtKind::kDelay);
  ASSERT_NE(outer->body, nullptr);
  EXPECT_EQ(outer->body->kind, StmtKind::kEventControl);
  ASSERT_NE(outer->body->body, nullptr);
  EXPECT_EQ(outer->body->body->kind, StmtKind::kBlockingAssign);
}

TEST(TimingControlSyntaxParsing, NestedEventControlWrappingDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) #10 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->kind, StmtKind::kEventControl);
  ASSERT_NE(outer->body, nullptr);
  EXPECT_EQ(outer->body->kind, StmtKind::kDelay);
  ASSERT_NE(outer->body->body, nullptr);
  EXPECT_EQ(outer->body->body->kind, StmtKind::kBlockingAssign);
}

}  // namespace
