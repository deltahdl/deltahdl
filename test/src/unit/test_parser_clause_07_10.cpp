// §7.10: Queues

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, VarDeclAssignmentQueueDim) {
  auto r = Parse("module m; int q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "q");
}

};

// ---------------------------------------------------------------------------
// variable_dimension ::= unsized_dimension | unpacked_dimension
//                       | associative_dimension | queue_dimension
// (This is a union production; each alternative is tested above/below.)
// ---------------------------------------------------------------------------
TEST(ParserA25, VarDimAllFourAlternatives) {
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
  // unsized_dimension: nullptr sentinel
  ASSERT_EQ(items[0]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[0]->unpacked_dims[0], nullptr);
  // unpacked_dimension: range
  ASSERT_EQ(items[1]->unpacked_dims.size(), 1u);
  ASSERT_NE(items[1]->unpacked_dims[0], nullptr);
  EXPECT_EQ(items[1]->unpacked_dims[0]->kind, ExprKind::kBinary);
  // associative_dimension: string type
  ASSERT_EQ(items[2]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[2]->unpacked_dims[0]->text, "string");
  // queue_dimension: $
  ASSERT_EQ(items[3]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[3]->unpacked_dims[0]->text, "$");
}

// ---------------------------------------------------------------------------
// queue_dimension ::= [ $ [ : constant_expression ] ]
// ---------------------------------------------------------------------------
TEST(ParserA25, QueueDimUnbounded) {
  auto r = Parse("module m; int q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  EXPECT_EQ(item->unpacked_dims[0]->rhs, nullptr);
}

}  // namespace
