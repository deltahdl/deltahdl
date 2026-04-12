#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ForceReleaseParsing, ForceWithConcat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin force {a, b} = 2'b11; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ForceReleaseParsing, ReleaseWithConcat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release {a, b}; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}
TEST(ForceReleaseParsing, ForceNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    force bus = 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ForceReleaseParsing, ReleaseNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    release bus;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  ASSERT_NE(stmt->lhs, nullptr);
}


TEST(ForceReleaseParsing, ForceVariableParses) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    force sig = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ForceReleaseParsing, ReleaseVariableParses) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    release sig;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ForceReleaseParsing, VarLvalueForce) {
  auto r = Parse("module m; logic x; initial force x = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ForceReleaseParsing, VarLvalueRelease) {
  auto r = Parse(
      "module m; logic x;\n"
      "  initial begin force x = 1; release x; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ForceReleaseParsing, ForceConstBitSelectNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    force bus[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ForceReleaseParsing, ForceConstPartSelectNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    force bus[7:4] = 4'hF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ForceReleaseParsing, ReleaseConstBitSelectNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    release bus[3];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ForceReleaseParsing, ReleaseConstPartSelectNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    release bus[7:4];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

}  // namespace
