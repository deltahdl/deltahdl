// §10.3.1: The net declaration assignment

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfNetDeclAssignmentsWithInit) {
  auto r = Parse("module m; wire a = 1'b0, b = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(ParserA24, NetDeclAssignmentWithInit) {
  auto r = Parse("module m; wire w = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserA24, NetDeclAssignmentDimsAndInit) {
  auto r = Parse("module m; wire [7:0] mem [0:3] = '{0,1,2,3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

}  // namespace
