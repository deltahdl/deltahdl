#include <gtest/gtest.h>

#include <format>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(SingularAggregateTypes, SingularVectorPortDefaultAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t(input logic [7:0] p = 8'hAA);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SingularAggregateTypes, UnpackedArrayPortDefaultRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t(input logic [7:0] p [0:3] = '{8'h0, 8'h0, 8'h0, 8'h0});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on non-singular port 'p'", 1,
                            "23.2.2.4"));
}

TEST(SingularAggregateTypes, PackedStructPortDefaultAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef struct packed { logic [7:0] a; } ps_t;\n"
      "module t(input ps_t p = '0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SingularAggregateTypes, InlineUnpackedStructPortDefaultRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t(input struct { logic [7:0] a; } p = '{a: 8'h0});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on non-singular port 'p'", 1,
                            "23.2.2.4"));
}

TEST(SingularAggregateTypes, TypedefUnpackedStructPortDefaultRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef struct { logic [7:0] a; } us_t;\n"
      "module t(input us_t p = '{a: 8'h0});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on non-singular port 'p'", 2,
                            "23.2.2.4"));
}

TEST(SingularAggregateTypes, TypedefUnpackedUnionPortDefaultRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef union { logic [7:0] a; logic [7:0] b; } uu_t;\n"
      "module t(input uu_t p = '{a: 8'h0});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on non-singular port 'p'", 2,
                            "23.2.2.4"));
}

TEST(SingularAggregateTypes, StringPortDefaultAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t(input var string p = \"hi\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SingularAggregateTypes, EnumPortDefaultAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef enum { A, B } e_t;\n"
      "module t(input var e_t p = A);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SingularAggregateTypes, PackedUnionPortDefaultAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef union packed { logic [7:0] a; logic [7:0] b; } pu_t;\n"
      "module t(input pu_t p = '0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SingularAggregateTypes, UnpackedArrayOfPackedStructPortDefaultRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef struct packed { logic [7:0] a; } ps_t;\n"
      "module t(input ps_t p [0:1] = '{'0, '0});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on non-singular port 'p'", 2,
                            "23.2.2.4"));
}

TEST(SingularAggregateTypes, NonEquivalentUnpackedStructComparisonRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef struct { logic [7:0] a; } s1_t;\n"
      "typedef struct { logic [15:0] b; } s2_t;\n"
      "module t;\n"
      "  s1_t x;\n"
      "  s2_t y;\n"
      "  logic r;\n"
      "  initial r = (x == y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "comparison of non-equivalent aggregate types 's1_t' and 's2_t'", 7,
      "6.22.2"));
}

TEST(SingularAggregateTypes, SingularNamedOperandComparisonAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef int i1_t;\n"
      "typedef int i2_t;\n"
      "module t;\n"
      "  i1_t x;\n"
      "  i2_t y;\n"
      "  logic r;\n"
      "  initial r = (x == y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

TEST(SingularAggregateTypes, ClassHandlePortDefaultAccepted) {
  constexpr const char* kClasses =
      "package p;\n"
      "  class PC;\n"
      "  endclass\n"
      "endpackage\n"
      "class C;\n"
      "endclass\n"
      "typedef C c_t;\n"
      "interface class IC;\n"
      "endclass\n"
      "class P #(int N = 1);\n"
      "endclass\n";
  for (const char* port : {"C h", "p::PC h", "c_t h", "IC h", "P #(8) h"}) {
    EXPECT_TRUE(ElabOk(std::format("{}module t(input {} = null);\nendmodule\n",
                                   kClasses, port)))
        << port;
  }
}

TEST(SingularAggregateTypes, ClassHandlePortDefaultAcceptedOnEveryHeader) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "endclass\n"
             "interface i(input C h = null);\n"
             "endinterface\n"
             "program q(input C h = null);\n"
             "endprogram\n"
             "module t;\n"
             "  i u();\n"
             "  q v();\n"
             "endmodule\n"));
}

TEST(SingularAggregateTypes, UnpackedArrayOfClassHandlesPortDefaultRejected) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "endclass\n"
      "module t(input C hs [2] = '{null, null});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on non-singular port 'hs'", 3,
                            "23.2.2.4"));
}

}  // namespace
