#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(DataTypeParsing, ValueSet_2StateBitDecl) {
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
