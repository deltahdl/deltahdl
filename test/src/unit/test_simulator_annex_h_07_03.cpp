#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_open_array_natural_order.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

namespace {

svOpenArrayHandle MakeHandle(void* data, const SvOpenArrayDimRange* ranges,
                             int n_dims, size_t elem_size,
                             SvOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->has_packed_part = 1;
  desc->ranges = ranges;
  desc->elem_size = elem_size;
  return desc;
}

TEST(DataRepresentation, NonPackedTypeIsCCompatible) {
  int data[4] = {10, 20, 30, 40};
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {0, 3}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, sizeof(int), &desc);

  for (int i = 0; i < 4; ++i) {
    void* p = svGetArrElemPtr1(h, i);
    EXPECT_EQ(p, static_cast<void*>(&data[i]));
    EXPECT_EQ(*static_cast<int*>(p), data[i]);
  }
}

TEST(DataRepresentation, SizedFormalAndStructEmbeddedAreCCompatible) {
  double data[3] = {1.5, -2.25, 100.0};
  const SvOpenArrayDimRange kRanges[] = {{63, 0}, {0, 2}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, sizeof(double), &desc);

  for (int i = 0; i < 3; ++i) {
    void* p = svGetArrElemPtr1(h, i);
    EXPECT_EQ(p, static_cast<void*>(&data[i]));
    EXPECT_EQ(*static_cast<double*>(p), data[i]);
  }
}

TEST(DataRepresentation, OpenArrayCCompatibleElementMatchesIndividualValue) {
  int data[5] = {0, 11, 22, 33, 44};
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {0, 4}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, sizeof(int), &desc);

  int* base = static_cast<int*>(svGetArrElemPtr1(h, 0));
  ASSERT_EQ(base, &data[0]);
  for (int i = 0; i < 5; ++i) {
    EXPECT_EQ(&base[i], static_cast<int*>(svGetArrElemPtr1(h, i)));
    EXPECT_EQ(base[i], data[i]);
  }
  EXPECT_EQ(static_cast<char*>(svGetArrElemPtr1(h, 1)) -
                static_cast<char*>(svGetArrElemPtr1(h, 0)),
            static_cast<long>(sizeof(int)));
}

TEST(DataRepresentation, OpenArrayPackedElementUsesCanonicalForm) {
  svBitVecVal data[4] = {0u, 0u, 0u, 0u};
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, 0, &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);
  EXPECT_EQ(svGetArrayPtr(h), nullptr);

  const svBitVecVal kIn = 0xA5u;
  svPutBitArrElem1VecVal(h, &kIn, 2);
  EXPECT_EQ(data[2], 0xA5u);
  svBitVecVal out = 0u;
  svGetBitArrElem1VecVal(&out, h, 2);
  EXPECT_EQ(out, 0xA5u);
}

TEST(DataRepresentation, OpenArrayScalarElementUsesCanonicalForm) {
  svLogicVecVal data[4] = {{0u, 0u}, {0u, 0u}, {0u, 0u}, {0u, 0u}};
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 3}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, 0, &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 1), nullptr);
  EXPECT_EQ(svGetArrayPtr(h), nullptr);

  const svLogic kStates[] = {sv_0, sv_1, sv_z, sv_x};
  for (svLogic s : kStates) {
    svPutLogicArrElem1(h, s, 1);
    EXPECT_EQ(svGetLogicArrElem1(h, 1), s);
  }
}

TEST(DataRepresentation, OpenArrayWidePackedElementUsesCanonicalForm) {
  svBitVecVal data[4] = {0u, 0u, 0u, 0u};
  const SvOpenArrayDimRange kRanges[] = {{39, 0}, {0, 1}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, 0, &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);

  const svBitVecVal kIn[2] = {0x12345678u, 0x9Au};
  svPutBitArrElem1VecVal(h, kIn, 1);
  EXPECT_EQ(data[2], 0x12345678u);
  EXPECT_EQ(data[3], 0x9Au);

  svBitVecVal out[2] = {0u, 0u};
  svGetBitArrElem1VecVal(out, h, 1);
  EXPECT_EQ(out[0], 0x12345678u);
  EXPECT_EQ(out[1], 0x9Au);
}

TEST(DataRepresentation, EnumRepresentedByBaseTypeWithoutNames) {
  const uint32_t kBaseValue = 0x2Cu;

  svLogicVecVal as_enum = {0u, 0u};
  svLogicVecVal as_integer = {0u, 0u};
  for (int bit = 0; bit < 32; ++bit) {
    svLogic v = ((kBaseValue >> bit) & 1u) ? sv_1 : sv_0;
    svPutBitselLogic(&as_enum, bit, v);
    svPutBitselLogic(&as_integer, bit, v);
  }

  EXPECT_EQ(as_enum.aval, as_integer.aval);
  EXPECT_EQ(as_enum.bval, as_integer.bval);
  EXPECT_EQ(as_enum.aval, kBaseValue);
  EXPECT_EQ(as_enum.bval, 0u);
  for (int bit = 0; bit < 32; ++bit) {
    EXPECT_EQ(svGetBitselLogic(&as_enum, bit),
              svGetBitselLogic(&as_integer, bit));
  }
}

TEST(DataRepresentation, EnumTimeBaseRepresentedAsWide4State) {
  const uint64_t kBaseValue = (static_cast<uint64_t>(0x100u) << 32) | 0x2Cu;

  svLogicVecVal as_enum[2] = {{0u, 0u}, {0u, 0u}};
  svLogicVecVal as_time[2] = {{0u, 0u}, {0u, 0u}};
  for (int bit = 0; bit < 64; ++bit) {
    svLogic v = ((kBaseValue >> bit) & 1u) ? sv_1 : sv_0;
    svPutBitselLogic(as_enum, bit, v);
    svPutBitselLogic(as_time, bit, v);
  }

  EXPECT_EQ(as_enum[0].aval, as_time[0].aval);
  EXPECT_EQ(as_enum[1].aval, as_time[1].aval);
  EXPECT_EQ(as_enum[0].aval, 0x2Cu);
  EXPECT_EQ(as_enum[1].aval, 0x100u);
  EXPECT_EQ(as_enum[0].bval, 0u);
  EXPECT_EQ(as_enum[1].bval, 0u);
  for (int bit = 0; bit < 64; ++bit) {
    EXPECT_EQ(svGetBitselLogic(as_enum, bit), svGetBitselLogic(as_time, bit));
  }
}

TEST(DataRepresentation, UnpackedNaturalOrderMinToZeroMaxToAbs) {
  struct Case {
    int l;
    int r;
  };
  const Case kCases[] = {{0, 7}, {7, 0}, {-1, -8}};
  for (const Case& c : kCases) {
    const SvOpenArrayDimRange kRanges[] = {{0, 0}, {c.l, c.r}};
    SvOpenArrayDesc desc;
    svOpenArrayHandle h = MakeHandle(nullptr, kRanges, 2, 0, &desc);

    ExpectUnpackedNaturalOrderMinToZeroMaxToAbs(h, 1, c.l, c.r);
  }
}

TEST(DataRepresentation, UnpackedSingleElementDimensionMapsToZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {-4, -4}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(nullptr, kRanges, 2, 0, &desc);

  EXPECT_EQ(svLow(h, 1), -4);
  EXPECT_EQ(svHigh(h, 1), -4);
  EXPECT_EQ(svSize(h, 1), 1);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 0);
}

TEST(DataRepresentation, UnpackedLowerIndicesGoFirst) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {3, -2}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(nullptr, kRanges, 2, 0, &desc);

  const int kLo = svLow(h, 1);
  const int kSize = svSize(h, 1);
  EXPECT_EQ(kLo, -2);
  EXPECT_EQ(kSize, 6);

  int expected_c = 0;
  for (int sv = kLo; sv < kLo + kSize; ++sv) {
    EXPECT_EQ(sv - kLo, expected_c);
    ++expected_c;
  }
  EXPECT_EQ(expected_c, kSize);
}

delta::DpiArg FormalOf(delta::DataTypeKind type, uint32_t width = 0) {
  delta::DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = delta::Direction::kInput;
  formal.width = width;
  return formal;
}

TEST(DpiDataRepresentation, EachFormalTakesTheRepresentationOfItsType) {
  using delta::DataTypeKind;
  using delta::DpiRepresentation;
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kInt)),
            DpiRepresentation::kBasic);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kReal)),
            DpiRepresentation::kBasic);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kString)),
            DpiRepresentation::kBasic);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kBit, 1)),
            DpiRepresentation::kBasic);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kBit, 8)),
            DpiRepresentation::kCanonical);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kInteger)),
            DpiRepresentation::kCanonical);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kTime)),
            DpiRepresentation::kCanonical);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kStruct)),
            DpiRepresentation::kCCompatible);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kUnion)),
            DpiRepresentation::kCCompatible);
  EXPECT_EQ(delta::DpiRepresentationOfFormal(FormalOf(DataTypeKind::kEvent)),
            DpiRepresentation::kNone);
}

TEST(DpiDataRepresentation, AnOpenArraysElementIsCanonicalOnlyWhenPacked) {
  using delta::DataTypeKind;
  using delta::DpiRepresentation;
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kBit),
            DpiRepresentation::kCanonical);
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kLogic),
            DpiRepresentation::kCanonical);
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kBit),
            DpiRepresentation::kCanonical);
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kInteger),
            DpiRepresentation::kCanonical);
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kInt),
            DpiRepresentation::kCCompatible);
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kReal),
            DpiRepresentation::kCCompatible);
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kChandle),
            DpiRepresentation::kCCompatible);
  EXPECT_EQ(delta::DpiRepresentationOfOpenArrayElement(DataTypeKind::kStruct),
            DpiRepresentation::kCCompatible);
}

TEST(DpiDataRepresentation, AnEnumIsItsBaseTypeAndSmallWhenItIs) {
  using delta::DataTypeKind;
  EXPECT_TRUE(delta::DpiEnumIsSmall(DataTypeKind::kInt, 0));
  EXPECT_TRUE(delta::DpiEnumIsSmall(DataTypeKind::kByte, 0));
  EXPECT_TRUE(delta::DpiEnumIsSmall(DataTypeKind::kShortint, 0));
  EXPECT_TRUE(delta::DpiEnumIsSmall(DataTypeKind::kLongint, 0));
  EXPECT_FALSE(delta::DpiEnumIsSmall(DataTypeKind::kInteger, 0));
  EXPECT_FALSE(delta::DpiEnumIsSmall(DataTypeKind::kTime, 0));
  EXPECT_FALSE(delta::DpiEnumIsSmall(DataTypeKind::kBit, 4));
  EXPECT_EQ(delta::DpiCTypeOfFormal(FormalOf(DataTypeKind::kInt), false),
            "const int");
  EXPECT_EQ(delta::DpiCTypeOfFormal(FormalOf(DataTypeKind::kInteger), false),
            "const svLogicVecVal*");
  EXPECT_EQ(delta::DpiCTypeOfFormal(FormalOf(DataTypeKind::kBit, 4), false),
            "const svBitVecVal*");
}

int LowBitsOf(const uint32_t* v) { return static_cast<int>(*v & 7U); }

int EnumPlusOne(int e) { return e + 1; }

int EnumBits(const SvLogicVecVal* e) {
  return static_cast<int>((e->aval * 10) + e->bval);
}

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(DpiTypesOfFormals, ATypeNameCrossesAsTheTypeItStandsFor) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  typedef bit [2:0] A;\n"
      "  typedef struct packed { bit a; bit b; bit c; } S;\n"
      "  typedef union packed { A a; S s; } U;\n"
      "  typedef enum int { P = 20, Q = 30 } E;\n"
      "  typedef enum logic [3:0] { X = 4'd5, Y = 4'b1z10 } F;\n"
      "  import \"DPI-C\" function int as_a(input A v);\n"
      "  import \"DPI-C\" function int as_s(input S v);\n"
      "  import \"DPI-C\" function int as_u(input U v);\n"
      "  import \"DPI-C\" function int as_e(input E e);\n"
      "  import \"DPI-C\" function int as_f(input F f);\n"
      "  int a, s, u, e, l;\n"
      "  S sv; U uv; F fv;\n"
      "  initial begin\n"
      "    sv.a = 1'b1; sv.b = 1'b0; sv.c = 1'b1;\n"
      "    uv.a = 3'b110;\n"
      "    fv = Y;\n"
      "    a = as_a(3'b011);\n"
      "    s = as_s(sv);\n"
      "    u = as_u(uv);\n"
      "    e = as_e(Q);\n"
      "    l = as_f(fv);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"as_a", reinterpret_cast<void*>(&LowBitsOf)},
       {"as_s", reinterpret_cast<void*>(&LowBitsOf)},
       {"as_u", reinterpret_cast<void*>(&LowBitsOf)},
       {"as_e", reinterpret_cast<void*>(&EnumPlusOne)},
       {"as_f", reinterpret_cast<void*>(&EnumBits)}},
      "annex_h_07_03_type_names");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "a"), 3U);
  EXPECT_EQ(VariableValue(f, "s"), 5U);
  EXPECT_EQ(VariableValue(f, "u"), 6U);
  EXPECT_EQ(VariableValue(f, "e"), 31U);
  EXPECT_EQ(VariableValue(f, "l"), 104U);
}

}  // namespace
