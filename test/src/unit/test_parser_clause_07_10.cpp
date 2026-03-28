#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(QueueDeclarationParsing, UnboundedQueueParsesAsVarDecl) {
  auto r = Parse("module m; int q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "q");
}

TEST(QueueDeclarationParsing, VarDimAllFourAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  int d [];       \n"
      "  int u [3:0];    \n"
      "  int a [string]; \n"
      "  int q [$];      \n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);

  ASSERT_EQ(items[0]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[0]->unpacked_dims[0], nullptr);

  ASSERT_EQ(items[1]->unpacked_dims.size(), 1u);
  ASSERT_NE(items[1]->unpacked_dims[0], nullptr);
  EXPECT_EQ(items[1]->unpacked_dims[0]->kind, ExprKind::kBinary);

  ASSERT_EQ(items[2]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[2]->unpacked_dims[0]->text, "string");

  ASSERT_EQ(items[3]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[3]->unpacked_dims[0]->text, "$");
}

TEST(QueueDeclarationParsing, QueueDimUnbounded) {
  auto r = Parse("module m; int q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  EXPECT_EQ(item->unpacked_dims[0]->rhs, nullptr);
}

TEST(QueueDeclarationParsing, QueueWithInitializer) {
  auto r = Parse(
      "module t;\n"
      "  integer Q[$] = '{3, 2, 7};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Q");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(QueueDeclarationParsing, QueueOfStrings) {
  auto r = Parse(
      "module t;\n"
      "  string names[$] = '{\"Bob\"};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "names");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(QueueDeclarationParsing, QueueDimBounded) {
  auto r = Parse("module m; int q [$:100]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  ASSERT_NE(item->unpacked_dims[0]->rhs, nullptr);
}

TEST(QueueDeclarationParsing, QueueWithBound) {
  auto r = Parse(
      "module t;\n"
      "  bit q2[$:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q2");
}
TEST(QueueDeclarationParsing, QueueBounded) {
  auto r = Parse(
      "module t;\n"
      "  bit q2[$:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q2");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(QueueDeclarationParsing, QueueWithMaxSize) {
  auto r = Parse(
      "module m;\n"
      "  int q[$:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
