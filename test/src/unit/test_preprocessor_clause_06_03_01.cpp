#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection6, ValueSet_4StateLogicDecl) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  logic [3:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(Is4stateType(DataTypeKind::kLogic));
}

// §6.3.1: reg is 4-state.
TEST(ParserSection6, ValueSet_4StateRegDecl) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  reg [7:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_TRUE(Is4stateType(DataTypeKind::kReg));
}

// §6.3.1: integer is 4-state.
TEST(ParserSection6, ValueSet_4StateIntegerDecl) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  integer i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_TRUE(Is4stateType(DataTypeKind::kInteger));
}

// §6.3.1: bit is 2-state (only 0/1).
TEST(ParserSection6, ValueSet_2StateBitDecl) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  bit [3:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(Is4stateType(DataTypeKind::kBit));
}

// §6.3.1: int is 2-state.
TEST(ParserSection6, ValueSet_2StateIntDecl) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  int x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(Is4stateType(DataTypeKind::kInt));
}

// §6.3.1: byte is 2-state.
TEST(ParserSection6, ValueSet_2StateByteDecl) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_FALSE(Is4stateType(DataTypeKind::kByte));
}

}  // namespace
