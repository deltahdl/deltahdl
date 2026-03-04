// §7.5: Dynamic arrays

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// unsized_dimension ::= [ ]
// ---------------------------------------------------------------------------
TEST(ParserA25, UnsizedDimDynamicArray) {
  auto r = Parse("module m; int d []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}
// =========================================================================
// §7.5: Dynamic arrays
// =========================================================================
TEST(ParserSection7, DynamicArrayDecl) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "dyn");
  EXPECT_FALSE(item->unpacked_dims.empty());
}
// --- Test helpers ---
TEST(ParserSection7, DynamicArrayMultiDim) {
  auto r = Parse(
      "module t;\n"
      "  integer mem[2][];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "mem");
}

}  // namespace
