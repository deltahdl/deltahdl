#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// §6.11 Table 6-8: byte is an 8-bit integer.
TEST(IntegerDataTypes, ByteIsEightBits) {
  DataType dt;
  dt.kind = DataTypeKind::kByte;
  EXPECT_EQ(EvalTypeWidth(dt), 8u);
}

// §6.11 Table 6-8: shortint is a 16-bit integer.
TEST(IntegerDataTypes, ShortintIsSixteenBits) {
  DataType dt;
  dt.kind = DataTypeKind::kShortint;
  EXPECT_EQ(EvalTypeWidth(dt), 16u);
}

// §6.11 Table 6-8: int is a 32-bit integer.
TEST(IntegerDataTypes, IntIsThirtyTwoBits) {
  DataType dt;
  dt.kind = DataTypeKind::kInt;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
}

// §6.11 Table 6-8: longint is a 64-bit integer.
TEST(IntegerDataTypes, LongintIsSixtyFourBits) {
  DataType dt;
  dt.kind = DataTypeKind::kLongint;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

// §6.11 Table 6-8: integer is a 32-bit integer.
TEST(IntegerDataTypes, IntegerIsThirtyTwoBits) {
  DataType dt;
  dt.kind = DataTypeKind::kInteger;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
}

// §6.11 Table 6-8: time is a 64-bit integer.
TEST(IntegerDataTypes, TimeIsSixtyFourBits) {
  DataType dt;
  dt.kind = DataTypeKind::kTime;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

// §6.11 Table 6-8: predefined widths propagate from the parsed declaration
// through the elaborator into RtlirVariable.width for every predefined-width
// integer type when no packed range is given.
TEST(IntegerDataTypes, PredefinedWidthsFlowIntoRtlirVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte b;\n"
      "  shortint s;\n"
      "  int i;\n"
      "  longint l;\n"
      "  integer ig;\n"
      "  time tm;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  std::unordered_map<std::string_view, uint32_t> width_by_name;
  for (const auto& v : mod->variables) width_by_name[v.name] = v.width;
  EXPECT_EQ(width_by_name["b"], 8u);
  EXPECT_EQ(width_by_name["s"], 16u);
  EXPECT_EQ(width_by_name["i"], 32u);
  EXPECT_EQ(width_by_name["l"], 64u);
  EXPECT_EQ(width_by_name["ig"], 32u);
  EXPECT_EQ(width_by_name["tm"], 64u);
}

// §6.11 Table 6-8: bit, logic, and reg have user-defined vector size — the
// width comes from the declared range, not from a predefined-width fallback.
TEST(IntegerDataTypes, UserDefinedVectorSizeHonorsRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit   [11:0] bv;\n"
      "  logic [23:0] lv;\n"
      "  reg   [ 6:0] rv;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  std::unordered_map<std::string_view, uint32_t> width_by_name;
  for (const auto& v : mod->variables) width_by_name[v.name] = v.width;
  EXPECT_EQ(width_by_name["bv"], 12u);
  EXPECT_EQ(width_by_name["lv"], 24u);
  EXPECT_EQ(width_by_name["rv"], 7u);
}

}  // namespace
