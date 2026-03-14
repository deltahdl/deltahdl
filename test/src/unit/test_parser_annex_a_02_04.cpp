#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DeclarationAssignmentParsing, NetDeclAssignmentBasic) {
  auto r = Parse("module m; wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_EQ(item->init_expr, nullptr);
}

TEST(DeclarationAssignmentParsing, NetDeclAssignmentWithUnpackedDims) {
  auto r = Parse("module m; wire w [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(DeclarationAssignmentParsing, ParamAssignmentBasic) {
  auto r = Parse("module m; parameter WIDTH = 8; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "WIDTH");
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
