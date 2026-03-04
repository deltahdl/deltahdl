// §7.3: Unions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// §7.3: Unions
// =========================================================================
TEST(ParserSection7, UnionBasic) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    int i;\n"
      "    shortreal f;\n"
      "  } num;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

}  // namespace
