#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// §6.4: Singular types — all types except unpacked struct, unpacked union,
// unpacked array.

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

// §6.4: string is singular even though it can be indexed like an unpacked
// array of bytes.
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

// §6.4: Packed struct is singular.
TEST(SingularAggregateTypes, PackedStructIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kStruct;
  dt.is_packed = true;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

// §6.4: Packed union is singular.
TEST(SingularAggregateTypes, PackedUnionIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kUnion;
  dt.is_packed = true;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

// §6.4: Unpacked struct is aggregate.
TEST(SingularAggregateTypes, UnpackedStructIsAggregate) {
  DataType dt;
  dt.kind = DataTypeKind::kStruct;
  dt.is_packed = false;
  EXPECT_FALSE(IsSingularType(dt));
  EXPECT_TRUE(IsAggregateType(dt));
}

// §6.4: Unpacked union is aggregate.
TEST(SingularAggregateTypes, UnpackedUnionIsAggregate) {
  DataType dt;
  dt.kind = DataTypeKind::kUnion;
  dt.is_packed = false;
  EXPECT_FALSE(IsSingularType(dt));
  EXPECT_TRUE(IsAggregateType(dt));
}

// §6.4: Net types are singular.
TEST(SingularAggregateTypes, WireIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kWire;
  EXPECT_TRUE(IsSingularType(dt));
}

TEST(SingularAggregateTypes, TriIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTri;
  EXPECT_TRUE(IsSingularType(dt));
}

TEST(SingularAggregateTypes, TriregIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kTrireg;
  EXPECT_TRUE(IsSingularType(dt));
}

// §6.4: Integral types (§6.11.1) are always singular even though they can be
// sliced into multiple singular values.
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

// §6.4: Unpacked array makes a type aggregate — the variable has
// unpacked_size > 0.
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

// §6.4: Implicit type is singular.
TEST(SingularAggregateTypes, ImplicitIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kImplicit;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

// §6.4: VirtualInterface is singular (handle-like).
TEST(SingularAggregateTypes, VirtualInterfaceIsSingular) {
  DataType dt;
  dt.kind = DataTypeKind::kVirtualInterface;
  EXPECT_TRUE(IsSingularType(dt));
  EXPECT_FALSE(IsAggregateType(dt));
}

}  // namespace
