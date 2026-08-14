#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

// Exercises the right-hand branch of the queue_dimension BNF:
// `[ $ [ : constant_expression ] ]`. With the colon and bound present, the
// parser shall store the bound expression on the dim node's rhs.
TEST(QueueDeclarationParsing, QueueDimBoundedHasRhsExpr) {
  auto r = Parse("module m; int q [$:7]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  ASSERT_NE(item->unpacked_dims[0]->rhs, nullptr);
}

// Covers the `$` branch of Parser::ParseUnpackedDims in
// src/parser/parser_types.cpp, which builds the ExprKind::kIdentifier standing
// for a queue dimension. It assigned no range.start before this commit, and
// src/parser/parser_types.cpp assigned none at any site, so a report standing
// at the dimension printed "<unknown location>" instead of a file, line and
// column. §7.10 writes the dimension as `[ $ [ : constant_expression ] ]`, so
// the node begins at the `$`, at column 10 of line 2.
TEST(QueueDeclarationParsing, QueueDimStartsAtItsDollar) {
  auto r = Parse(
      "module m;\n"
      "  int q [$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->text, "$");
  EXPECT_EQ(dim->range.start.line, 2u);
  EXPECT_EQ(dim->range.start.column, 10u);
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

}  // namespace
