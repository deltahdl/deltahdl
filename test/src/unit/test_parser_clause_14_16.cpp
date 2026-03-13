#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SyncDriveParse, SimpleClockingDrive) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(SyncDriveParse, WithCycleDelay) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##2 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->cycle_delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(SyncDriveParse, CycleDelayNumber) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial cb.data <= ##3 8'h42;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, CycleDelayParenExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial cb.data <= ##(n+1) 8'h42;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, ClockvarBitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    output sig;\n"
              "  endclocking\n"
              "  initial dom.sig[2] <= 1'b1;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, ClockvarPartSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking bus @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial bus.data[3:0] <= 4'h5;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, InoutClockvarDrive) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    inout data;\n"
              "  endclocking\n"
              "  initial cb.data <= 8'hAB;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, MultipleDrivesInBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output a, b;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.a <= 1;\n"
      "    cb.b <= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SyncDriveParse, CycleDelayIdentifier) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial cb.data <= ##n 8'h42;\n"
              "endmodule\n"));
}

}  // namespace
