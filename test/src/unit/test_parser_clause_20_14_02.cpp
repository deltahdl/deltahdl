#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DistributionFunctionParsing, DistUniform) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_uniform(seed, 0, 100);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(DistributionFunctionParsing, DistNormal) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_normal(seed, 50, 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(DistributionFunctionParsing, DistExponential) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_exponential(seed, 5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(DistributionFunctionParsing, DistPoisson) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_poisson(seed, 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(DistributionFunctionParsing, DistChiSquare) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_chi_square(seed, 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// §20.14.2 Syntax 20-15: $dist_t ( seed , degree_of_freedom ).
TEST(DistributionFunctionParsing, DistT) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_t(seed, 4);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// §20.14.2 Syntax 20-15: $dist_erlang ( seed , k_stage , mean ) — the only
// distribution with three arguments after the seed.
TEST(DistributionFunctionParsing, DistErlang) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_erlang(seed, 2, 7);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

}
