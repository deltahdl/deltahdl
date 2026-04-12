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

TEST(TimingControlSyntaxParsing, ProceduralTimingControlEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_FALSE(stmt->events.empty());
  EXPECT_NE(stmt->body, nullptr);
}

TEST(TimingControlSyntaxParsing, ProceduralTimingControlEventNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

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

TEST(TimingControlSyntaxParsing, ProceduralTimingControlEventBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

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
