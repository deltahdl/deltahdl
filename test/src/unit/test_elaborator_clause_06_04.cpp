#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(SingularAggregateTypes, LogicIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, RegIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kReg;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, BitIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kBit;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, IntIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, IntegerIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kInteger;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, ByteIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kByte;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, ShortintIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kShortint;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, LongintIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kLongint;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, TimeIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTime;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, RealIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kReal;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, ShortrealIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, RealtimeIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kRealtime;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, StringIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kString;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, VoidIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kVoid;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, EventIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kEvent;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, ChandleIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kChandle;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, EnumIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, PackedStructIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kStruct;
  dt.is_packed = true;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, PackedUnionIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kUnion;
  dt.is_packed = true;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, UnpackedStructIsAggregate) {
  DataType dt;
  dt.kind = DataTypeKind::kStruct;
  dt.is_packed = false;
  EXPECT_FALSE(IsSingularType(dt));
  EXPECT_TRUE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, UnpackedUnionIsAggregate) {
  DataType dt;
  dt.kind = DataTypeKind::kUnion;
  dt.is_packed = false;
  EXPECT_FALSE(IsSingularType(dt));
  EXPECT_TRUE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, WireIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kWire;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, TriIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTri;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, TriregIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTrireg;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, WandIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kWand;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, WorIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kWor;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, TriandIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTriand;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, TriorIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTrior;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, Tri0IsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTri0;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, Tri1IsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTri1;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, Supply0IsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kSupply0;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, Supply1IsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kSupply1;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, UwireIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kUwire;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, NamedIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kNamed;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, LogicVectorIsSingular) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [31:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 0u);
}

TEST(SingularAggregateTypes, UnpackedArrayIsAggregate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_GT(mod->variables[0].unpacked_size, 0u);
}

TEST(SingularAggregateTypes, ImplicitIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kImplicit;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

TEST(SingularAggregateTypes, VirtualInterfaceIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kVirtualInterface;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

}  // namespace
