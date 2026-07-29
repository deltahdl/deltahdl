#include "fixture_parser.h"

using namespace delta;

namespace {

// A list_of_net_decl_assignments declares one net per element; the A.2.3
// sibling file checks that each element also carries its own initializer.
TEST(DeclarationListParsing, ListOfNetDeclAssignmentsOneNetPerElement) {
  auto r = Parse("module m; wire a = 1'b0, b = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 2);
}

// §10.3.1: the net declaration assignment is the net declaration form of a
// continuous assignment, placed on the net in the statement that declares it.
// The A.2.4 sibling file covers the same `[ = expression ]` branch of the
// net_decl_assignment production.
TEST(DeclarationAssignmentParsing, NetDeclAssignmentContinuousAssignForm) {
  auto r = Parse("module m; wire w = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(DeclarationAssignmentParsing, NetDeclAssignmentDimsAndInit) {
  auto r = Parse("module m; wire [7:0] mem [0:3] = '{0,1,2,3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

}  // namespace
