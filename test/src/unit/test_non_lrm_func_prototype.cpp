// §non-lrm:func_prototype

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA26, FuncPrototypeExternVoid) {
  auto r = Parse(
      "module m;\n"
      "  extern function void bar();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

}  // namespace
