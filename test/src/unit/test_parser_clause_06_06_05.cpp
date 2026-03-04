// §6.6.5: Tri0 and tri1 nets

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §6.7.1: Tri0 net declaration.
TEST(ParserSection6, Sec6_7_1_Tri0Decl) {
  auto r = Parse("module t;\n"
                 "  tri0 t0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri0);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Tri1 net declaration.
TEST(ParserSection6, Sec6_7_1_Tri1Decl) {
  auto r = Parse("module t;\n"
                 "  tri1 t1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri1);
  EXPECT_TRUE(item->data_type.is_net);
}

} // namespace
