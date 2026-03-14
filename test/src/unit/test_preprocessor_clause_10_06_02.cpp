#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AssignmentParsing, ForceKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AssignmentParsing, ForceLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "w");
}

TEST(AssignmentParsing, ReleaseKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    release w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  EXPECT_EQ(stmt->rhs, nullptr);
}

TEST(AssignmentParsing, ReleaseLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    release w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "w");
}
TEST(AssignmentParsing, ForceThenRelease) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "    release w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kForce);
  EXPECT_EQ(s1->kind, StmtKind::kRelease);
}

}  // namespace
