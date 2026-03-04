// §6.11.2: 2-state (two-value) and 4-state (four-value) data types

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection6, ValueSet_2StateBitDecl) {
  // §6.3: bit is a 2-state type (only 0 and 1).
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  bit [7:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(Is4stateType(DataTypeKind::kBit));
}

}  // namespace
