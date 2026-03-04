// §6.6.4: Trireg net

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// 21. Trireg net declaration.
TEST(ParserSection6, Sec6_5_TriregDecl) {
  auto r = Parse("module t;\n"
                 "  trireg cap;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "cap");
}

} // namespace
