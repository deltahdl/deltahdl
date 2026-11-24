#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

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

void SeeByte(signed char v) { SeeInC({v}); }
void SeeUnsignedByte(unsigned char v) { SeeInC({v}); }
void SeeShort(short v) { SeeInC({v}); }
void SeeInt(int v) { SeeInC({v}); }
void SeeUnsigned(unsigned v) { SeeInC({v}); }
void SeeLong(long long v) { SeeInC({v}); }
void SeeTwoChunks(const svBitVecVal* v) { SeeInC({v[0], v[1] & 0xFFU}); }
void SeeOneLogicChunk(const svLogicVecVal* v) { SeeInC({v->aval, v->bval}); }
void SeeTwoLogicChunks(const svLogicVecVal* v) {
  SeeInC({v[0].aval, v[0].bval, v[1].aval, v[1].bval});
}
void GiveByte(signed char* v) { *v = -5; }
void AddToShort(short* v) { *v = static_cast<short>(*v + 1); }
void GiveFourBits(svLogicVecVal* v) { *v = {0xCU, 0x5U}; }
void RunEnums(const std::string& items, SimFixture& f) {
  RunModuleWithC(items, f,
                 {{"see_byte", CAddress(&SeeByte)},
                  {"see_ubyte", CAddress(&SeeUnsignedByte)},
                  {"see_short", CAddress(&SeeShort)},
                  {"see_int", CAddress(&SeeInt)},
                  {"see_uint", CAddress(&SeeUnsigned)},
                  {"see_long", CAddress(&SeeLong)},
                  {"see_two", CAddress(&SeeTwoChunks)},
                  {"see_logic", CAddress(&SeeOneLogicChunk)},
                  {"see_two_logic", CAddress(&SeeTwoLogicChunks)},
                  {"give_byte", CAddress(&GiveByte)},
                  {"add_to_short", CAddress(&AddToShort)},
                  {"give_four", CAddress(&GiveFourBits)}},
                 "annex_h_07_03_enums");
}

TEST(DpiEnumRepresentation, AnIntegerAtomBaseCrossesByValue) {
  SimFixture f;
  RunEnums(
      "  typedef enum byte {BA = -5} eb;\n"
      "  typedef enum shortint {SA = -300} es;\n"
      "  typedef enum longint {LA = -64'sd5000000000} el;\n"
      "  import \"DPI-C\" function void see_byte(input eb e);\n"
      "  import \"DPI-C\" function void see_short(input es e);\n"
      "  import \"DPI-C\" function void see_long(input el e);\n"
      "  initial begin see_byte(BA); see_short(SA); see_long(LA); end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{-5, -300, -5000000000LL}));
}

TEST(DpiEnumRepresentation, AnUnsignedBaseKeepsItsWholeRange) {
  SimFixture f;
  RunEnums(
      "  typedef enum byte unsigned {BA = 200} eb;\n"
      "  typedef enum int unsigned {IA = 32'd4294967040} ei;\n"
      "  import \"DPI-C\" function void see_ubyte(input eb e);\n"
      "  import \"DPI-C\" function void see_uint(input ei e);\n"
      "  initial begin see_ubyte(BA); see_uint(IA); end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{200, 4294967040LL}));
}

TEST(DpiEnumRepresentation, TheDefaultBaseCrossesAsAnInt) {
  SimFixture f;
  RunEnums(
      "  typedef enum {A = -70000, B} e_t;\n"
      "  import \"DPI-C\" function void see_int(input e_t e);\n"
      "  initial begin see_int(A); see_int(B); end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{-70000, -69999}));
}

TEST(DpiEnumRepresentation, ABitVectorBaseCrossesAsItsCanonicalArray) {
  SimFixture f;
  RunEnums(
      "  typedef enum bit [39:0] {A = 40'hab_0000_0001} e_t;\n"
      "  import \"DPI-C\" function void see_two(input e_t e);\n"
      "  initial see_two(A);\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 0xAB}));
}

TEST(DpiEnumRepresentation, AnIntegerBaseCrossesAsAFourStateArray) {
  SimFixture f;
  RunEnums(
      "  typedef enum integer {A = 32'h1x0z} e_t;\n"
      "  import \"DPI-C\" function void see_logic(input e_t e);\n"
      "  initial see_logic(A);\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x1F00, 0x0F0F}));
}

TEST(DpiEnumRepresentation, ATimeBaseCrossesAsTwoFourStateChunks) {
  SimFixture f;
  RunEnums(
      "  typedef enum time {A = 64'h1234_5678_9abc_zzzz} e_t;\n"
      "  import \"DPI-C\" function void see_two_logic(input e_t e);\n"
      "  initial see_two_logic(A);\n",
      f);
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{0x9ABC0000LL, 0xFFFF, 0x12345678, 0}));
}

TEST(DpiEnumRepresentation, AnOutputOrAnInoutIsWrittenInTheBaseType) {
  SimFixture f;
  RunEnums(
      "  typedef enum byte {BA = -5, BB = 3} eb;\n"
      "  typedef enum shortint {SA = -300, SB = -299} es;\n"
      "  typedef enum logic [3:0] {VA = 4'b1x0z, VB = 4'b0001} ev;\n"
      "  import \"DPI-C\" function void give_byte(output eb e);\n"
      "  import \"DPI-C\" function void add_to_short(inout es e);\n"
      "  import \"DPI-C\" function void give_four(output ev e);\n"
      "  eb b = BB;\n"
      "  es s = SA;\n"
      "  ev v = VB;\n"
      "  bit ob, os, ov;\n"
      "  initial begin\n"
      "    give_byte(b); add_to_short(s); give_four(v);\n"
      "    ob = b == BA; os = s == SB; ov = v === VA;\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "ob"), 1U);
  EXPECT_EQ(DesignValue(f, "os"), 1U);
  EXPECT_EQ(DesignValue(f, "ov"), 1U);
}

int& FirstCell() {
  static int cell = 41;
  return cell;
}

int& SecondCell() {
  static int cell = 42;
  return cell;
}

void* HandleOf(int which) { return which == 0 ? &FirstCell() : &SecondCell(); }

template <typename Element>
const Element& ElementAt(svOpenArrayHandle h, int i) {
  return *static_cast<const Element*>(svGetArrElemPtr1(h, i));
}

void SeeReals(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    SeeInC({static_cast<long long>(ElementAt<double>(h, i) * 100)});
  }
}

void SeeShortreals(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    SeeInC({static_cast<long long>(ElementAt<float>(h, i) * 100)});
  }
}

void SeeHandles(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    SeeInC({*static_cast<int*>(ElementAt<void*>(h, i))});
  }
}

void SeeStrings(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    const char* const kText = ElementAt<const char*>(h, i);
    SeeInC({kText[0], static_cast<long long>(std::strlen(kText))});
  }
}

void SeeBytes(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    SeeInC({ElementAt<signed char>(h, i)});
  }
}

void SeeLogics(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    SeeInC({svGetLogicArrElem1(h, i)});
  }
}

void RunOpenElements(const std::string& items, SimFixture& f) {
  RunModuleWithC(items, f,
                 {{"see_reals", CAddress(&SeeReals)},
                  {"see_shortreals", CAddress(&SeeShortreals)},
                  {"see_handles", CAddress(&SeeHandles)},
                  {"see_strings", CAddress(&SeeStrings)},
                  {"see_bytes", CAddress(&SeeBytes)},
                  {"see_logics", CAddress(&SeeLogics)},
                  {"handle_of", CAddress(&HandleOf)}},
                 "annex_h_07_03_open_elements");
}

TEST(DpiOpenArrayElements, RealsAreReachedAsDoublesAndFloats) {
  SimFixture f;
  RunOpenElements(
      "  import \"DPI-C\" function void see_reals(input real a []);\n"
      "  import \"DPI-C\" function void see_shortreals(input shortreal a "
      "[]);\n"
      "  real r [2:3] = '{1.5, -2.25};\n"
      "  shortreal s [2:3] = '{0.5, -3.75};\n"
      "  initial begin see_reals(r); see_shortreals(s); end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{150, -225, 50, -375}));
}

TEST(DpiOpenArrayElements, ChandlesAreReachedAsPointers) {
  SimFixture f;
  RunOpenElements(
      "  import \"DPI-C\" function chandle handle_of(input int which);\n"
      "  import \"DPI-C\" function void see_handles(input chandle a []);\n"
      "  chandle h [2:3];\n"
      "  initial begin\n"
      "    h[2] = handle_of(0); h[3] = handle_of(1);\n"
      "    see_handles(h);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{41, 42}));
}

TEST(DpiOpenArrayElements, StringsAreReachedAsCStrings) {
  SimFixture f;
  RunOpenElements(
      "  import \"DPI-C\" function void see_strings(input string a []);\n"
      "  string s [2:3] = '{\"abc\", \"zygote\"};\n"
      "  initial see_strings(s);\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{'a', 3, 'z', 6}));
}

TEST(DpiOpenArrayElements, BytesAreReachedAsChars) {
  SimFixture f;
  RunOpenElements(
      "  import \"DPI-C\" function void see_bytes(input byte a []);\n"
      "  byte b [2:4] = '{-5, 7, 100};\n"
      "  initial see_bytes(b);\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{-5, 7, 100}));
}

TEST(DpiOpenArrayElements, ScalarLogicsKeepTheirFourStates) {
  SimFixture f;
  RunOpenElements(
      "  import \"DPI-C\" function void see_logics(input logic a []);\n"
      "  logic l [2:5] = '{1'bx, 1'bz, 1'b1, 1'b0};\n"
      "  initial see_logics(l);\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{sv_x, sv_z, sv_1, sv_0}));
}

void SizedReals(const double* a) {
  SeeInC(
      {static_cast<long long>(a[0] * 100), static_cast<long long>(a[1] * 100)});
}

void SizedShorts(const short* a) { SeeInC({a[0], a[1]}); }

void SizedHandles(void* const* a) {
  SeeInC({*static_cast<int*>(a[0]), *static_cast<int*>(a[1])});
}

void SizedStrings(const char* const* a) { SeeInC({a[0][0], a[1][0]}); }

void SizedScalars(const svScalar* a) { SeeInC({a[0], a[1], a[2]}); }

TEST(DpiSizedArrayElements, EachIsLaidOutAsItsTableType) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function chandle handle_of(input int which);\n"
      "  import \"DPI-C\" function void reals(input real a [0:1]);\n"
      "  import \"DPI-C\" function void shorts(input shortint a [0:1]);\n"
      "  import \"DPI-C\" function void handles(input chandle a [0:1]);\n"
      "  import \"DPI-C\" function void strings(input string a [0:1]);\n"
      "  import \"DPI-C\" function void bits(input bit a [0:2]);\n"
      "  import \"DPI-C\" function void logics(input logic a [0:2]);\n"
      "  real r [0:1] = '{1.5, -2.25};\n"
      "  shortint s [0:1] = '{-300, 7};\n"
      "  chandle h [0:1];\n"
      "  string t [0:1] = '{\"abc\", \"zygote\"};\n"
      "  bit b [0:2] = '{1, 0, 1};\n"
      "  logic l [0:2] = '{1'bx, 1'bz, 1'b1};\n"
      "  initial begin\n"
      "    h[0] = handle_of(0); h[1] = handle_of(1);\n"
      "    reals(r); shorts(s); handles(h); strings(t); bits(b); logics(l);\n"
      "  end\n",
      f,
      {{"handle_of", CAddress(&HandleOf)},
       {"reals", CAddress(&SizedReals)},
       {"shorts", CAddress(&SizedShorts)},
       {"handles", CAddress(&SizedHandles)},
       {"strings", CAddress(&SizedStrings)},
       {"bits", CAddress(&SizedScalars)},
       {"logics", CAddress(&SizedScalars)}},
      "annex_h_07_03_sized_elements");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{150, -225, -300, 7, 41, 42, 'a', 'z', 1, 0,
                                    1, sv_x, sv_z, sv_1}));
}

}  // namespace
