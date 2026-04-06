#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(RandcaseSyntaxParsing, RandcaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      50: x = 1;\n"
      "      30: x = 2;\n"
      "      20: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 3u);
}

TEST(RandcaseSyntaxParsing, RandcaseWithBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      50: begin x = 1; y = 2; end\n"
      "      50: begin x = 3; y = 4; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 2u);
}

TEST(RandcaseSyntaxParsing, RandcaseStmt) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : $display(\"one\");\n"
      "      2 : $display(\"two\");\n"
      "      3 : $display(\"three\");\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST_F(VerifyParseTest, RandcaseInModule) {
  auto* unit = Parse(R"(
    module m;
      initial begin
        randcase
          3 : x = 1;
          1 : x = 2;
        endcase
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_FALSE(items.empty());
}

TEST_F(VerifyParseTest, RandcaseSingleBranch) {
  auto* unit = Parse(R"(
    module m;
      initial begin
        randcase
          1 : y = 42;
        endcase
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST(RandcaseSyntaxParsing, RandcaseAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: a = 1;\n"
      "      1: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
}

TEST(RandcaseSyntaxParsing, RandcaseVaryingWeights) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      10: x = 1;\n"
      "      30: x = 2;\n"
      "      60: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 3u);
}

TEST(RandcaseSyntaxParsing, RandcaseSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: x = 42;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 1u);
}

TEST(RandcaseSyntaxParsing, RandcaseZeroWeight) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      0: x = 1;\n"
      "      0: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 2u);
}

TEST(RandcaseSyntaxParsing, RandcaseWeightExpressionsStored) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      10: x = 1;\n"
      "      20: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  ASSERT_EQ(stmt->randcase_items.size(), 2u);
  EXPECT_NE(stmt->randcase_items[0].first, nullptr);
  EXPECT_NE(stmt->randcase_items[1].first, nullptr);
  EXPECT_NE(stmt->randcase_items[0].second, nullptr);
  EXPECT_NE(stmt->randcase_items[1].second, nullptr);
}

}  // namespace
