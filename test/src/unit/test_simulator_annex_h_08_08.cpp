#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

TEST(DpiInoutAndOutputArguments, AlwaysPassedByReferenceUnlessAnOpenArray) {
  for (const Direction kDirection : {Direction::kOutput, Direction::kInout}) {
    EXPECT_EQ(
        DpiPassingModeOfFormal(Formal(DataTypeKind::kInt, kDirection), false),
        DpiPassingMode::kByReference);
    EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kInt, kDirection), false),
              "int*");
    EXPECT_EQ(
        DpiCTypeOfFormal(Formal(DataTypeKind::kBit, kDirection, 8), false),
        "svBitVecVal*");
    EXPECT_EQ(
        DpiCTypeOfFormal(Formal(DataTypeKind::kLogic, kDirection, 40), false),
        "svLogicVecVal*");
    EXPECT_EQ(
        DpiCTypeOfFormal(Formal(DataTypeKind::kInteger, kDirection), false),
        "svLogicVecVal*");
    EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kTime, kDirection), false),
              "svLogicVecVal*");
    EXPECT_EQ(
        DpiPassingModeOfFormal(Formal(DataTypeKind::kBit, kDirection, 8), true),
        DpiPassingMode::kByHandle);
    EXPECT_TRUE(DpiOutputOrInoutIsPassedByReference(
        Formal(DataTypeKind::kInt, kDirection), false));
    EXPECT_FALSE(DpiOutputOrInoutIsPassedByReference(
        Formal(DataTypeKind::kBit, kDirection, 8), true));
  }
  EXPECT_FALSE(DpiOutputOrInoutIsPassedByReference(
      Formal(DataTypeKind::kInt, Direction::kInput), false));
}

TEST(DpiInoutAndOutputArguments, AnOutputsUnusedBitsFollowTheCanonicalRules) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_fill";
  func.sv_name = "fill";
  func.return_type = DataTypeKind::kVoid;
  DpiArg formal = Formal(DataTypeKind::kBit, Direction::kOutput, 8);
  formal.name = "v";
  func.args = {formal};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromLogicVecWords({SvLogicVecVal{0xFFFFFFABU, 0U}}, 8,
                                          DataTypeKind::kBit);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLogicVecWords(
      {SvLogicVecVal{0U, 0U}}, 8, DataTypeKind::kBit)};
  rt.CallImportWithArgs("fill", actuals);
  ASSERT_TRUE(actuals[0].IsWideVec());
  const uint32_t kChunk = actuals[0].AsLogicVecWords()[0].aval;
  EXPECT_EQ(kChunk, 0xFFFFFFABU);
  EXPECT_EQ(DpiCanonicalUnusedBits(8), 24U);
  EXPECT_EQ(DpiCanonicalLastElementWithUnusedBits(kChunk, 8, false), 0xABU);
}

void WriteIntegers(char* b, short* s, int* i, long long* l) {
  *b = -100;
  *s = -30000;
  *i = 70000;
  *l = 5000000000LL;
}

int output_cell = 0;

void WriteRealsAndHandle(float* f, double* d, void** p) {
  *f = 1.5F;
  *d = 2.25;
  *p = &output_cell;
}

void WriteScalarsAndBump(unsigned char* bit, unsigned char* logic, int* io) {
  *bit = 1;
  *logic = 2;
  *io += 100;
}

void WriteVectors(uint32_t* bits40, SvLogicVecVal* logic64,
                  SvLogicVecVal* integer, SvLogicVecVal* time) {
  bits40[0] = 0xFFFFFFFFU;
  bits40[1] = 0xFFFFFFFFU;
  logic64[0] = {0xFU, 0};
  logic64[1] = {0xF0000000U, 0x80000000U};
  integer[0] = {5, 1};
  time[0] = {5, 0};
  time[1] = {2, 0};
}

TEST(DpiInoutAndOutputArguments, SmallFormalsAreWrittenThroughTheirPointers) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("write_integers", DataTypeKind::kVoid,
              {CFormal("b", DataTypeKind::kByte, Direction::kOutput),
               CFormal("s", DataTypeKind::kShortint, Direction::kOutput),
               CFormal("i", DataTypeKind::kInt, Direction::kOutput),
               CFormal("l", DataTypeKind::kLongint, Direction::kOutput)}));
  b.dpi.RegisterImport(
      CImport("write_reals", DataTypeKind::kVoid,
              {CFormal("f", DataTypeKind::kShortreal, Direction::kOutput),
               CFormal("d", DataTypeKind::kReal, Direction::kOutput),
               CFormal("p", DataTypeKind::kChandle, Direction::kOutput)}));
  b.dpi.RegisterImport(
      CImport("write_scalars", DataTypeKind::kVoid,
              {CFormal("bit", DataTypeKind::kBit, Direction::kOutput),
               CFormal("logic", DataTypeKind::kLogic, Direction::kOutput),
               CFormal("io", DataTypeKind::kInt, Direction::kInout)}));
  b.Bind({{"write_integers", reinterpret_cast<void*>(&WriteIntegers)},
          {"write_reals", reinterpret_cast<void*>(&WriteRealsAndHandle)},
          {"write_scalars", reinterpret_cast<void*>(&WriteScalarsAndBump)}},
         "annex_h_08_08_small");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> integers = {
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kByte),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kShortint),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kInt),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kLongint)};
  b.Call("write_integers", integers);
  EXPECT_EQ(integers[0].AsInt(), -100);
  EXPECT_EQ(integers[1].AsInt(), -30000);
  EXPECT_EQ(integers[2].AsInt(), 70000);
  EXPECT_EQ(integers[3].AsLongint(), 5000000000LL);
  std::vector<DpiArgValue> reals = {
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kShortreal),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kReal),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kChandle)};
  b.Call("write_reals", reals);
  EXPECT_DOUBLE_EQ(reals[0].AsReal(), 1.5);
  EXPECT_DOUBLE_EQ(reals[1].AsReal(), 2.25);
  EXPECT_EQ(reals[2].AsChandle(), &output_cell);
  std::vector<DpiArgValue> scalars = {
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kBit),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kLogic),
      DpiArgValue::FromInt(23)};
  b.Call("write_scalars", scalars);
  EXPECT_EQ(scalars[0].AsBit(), 1);
  EXPECT_EQ(scalars[1].AsLogic(), 2);
  EXPECT_EQ(scalars[2].AsInt(), 123);
}

TEST(DpiInoutAndOutputArguments, PackedFormalsAreWrittenAsCanonicalArrays) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("write_vectors", DataTypeKind::kVoid,
              {CFormal("bits40", DataTypeKind::kBit, Direction::kOutput, 40),
               CFormal("logic64", DataTypeKind::kLogic, Direction::kOutput, 64),
               CFormal("integer", DataTypeKind::kInteger, Direction::kOutput),
               CFormal("time", DataTypeKind::kTime, Direction::kOutput)}));
  b.Bind({{"write_vectors", reinterpret_cast<void*>(&WriteVectors)}},
         "annex_h_08_08_packed");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> args = {
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kBit, 40),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kLogic, 64),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kInteger),
      DpiRuntime::UndeterminedOutputValue(DataTypeKind::kTime)};
  args[3].type = DataTypeKind::kTime;
  b.Call("write_vectors", args);
  ASSERT_EQ(args[0].AsLogicVecWords().size(), 2U);
  EXPECT_EQ(args[0].AsLogicVecWords()[0].aval, 0xFFFFFFFFU);
  EXPECT_EQ(args[0].AsLogicVecWords()[1].aval, 0xFFU);
  EXPECT_EQ(args[0].AsLogicVecWords()[1].bval, 0U);
  ASSERT_EQ(args[1].AsLogicVecWords().size(), 2U);
  EXPECT_EQ(args[1].AsLogicVecWords()[1].aval, 0xF0000000U);
  EXPECT_EQ(args[1].AsLogicVecWords()[1].bval, 0x80000000U);
  EXPECT_EQ(args[2].AsLogicVec().aval, 5U);
  EXPECT_EQ(args[2].AsLogicVec().bval, 1U);
  ASSERT_EQ(args[3].AsLogicVecWords().size(), 2U);
  EXPECT_EQ(args[3].AsLogicVecWords()[0].aval, 5U);
  EXPECT_EQ(args[3].AsLogicVecWords()[1].aval, 2U);
}

void ChangeVectors(svBitVecVal* b, svLogicVecVal* l, svLogicVecVal* i,
                   svLogicVecVal* t) {
  SeeInC({b[0], b[1] & 0xFFU, l[0].aval, l[0].bval, l[1].aval & 0xFFU,
          l[1].bval & 0xFFU});
  SeeInC({i->aval, i->bval, t[0].aval, t[0].bval, t[1].aval, t[1].bval});
  b[0] += 1;
  b[1] = 0xFFFFFF12U;
  l[0] = {0xFU, 0xFFU};
  l[1] = {0xFFFFFF81U, 0xFFFFFF80U};
  *i = {0xF0U, 0x0FU};
  t[0] = {1, 2};
  t[1] = {9, 0};
}

TEST(DpiInoutAndOutputArguments, PackedInoutsArriveAndAreCarriedBack) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void change(inout bit [39:0] b,\n"
      "      inout logic [39:0] l, inout integer i, inout time t);\n"
      "  bit [39:0] b = 40'hab_0000_0005;\n"
      "  logic [39:0] l = 40'h4x_0000_00z1;\n"
      "  integer i = 32'h0000_x0z3;\n"
      "  time t = 64'h0000_0003_0000_0004;\n"
      "  bit ok_l, ok_i, ok_t;\n"
      "  initial begin\n"
      "    change(b, l, i, t);\n"
      "    ok_l = l === {8'bx0000001, 24'h0, 8'hzx};\n"
      "    ok_t = t === {32'd9, 30'b0, 2'bz1};\n"
      "    ok_i = i === 32'h0000_00fz;\n"
      "  end\n",
      f, {{"change", CAddress(&ChangeVectors)}}, "annex_h_08_08_packed_inouts");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{5, 0xAB, 0x01, 0xF0, 0x4F, 0x0F,
                                               0xF003, 0xF0F0, 4, 0, 3, 0}));
  EXPECT_EQ(DesignValue(f, "b"), 0x1200000006ULL);
  EXPECT_EQ(DesignValue(f, "ok_l"), 1U);
  EXPECT_EQ(DesignValue(f, "ok_i"), 1U);
  EXPECT_EQ(DesignValue(f, "ok_t"), 1U);
}

int& HandleCell(int which) {
  static int cells[2] = {0, 0};
  return cells[which];
}

void* FirstHandle() { return &HandleCell(0); }

int HandleIsSecond(void* p) { return p == &HandleCell(1) ? 1 : 0; }

void ChangeNumbers(double* r, float* s, char* b, long long* l) {
  SeeInC({static_cast<long long>(*r * 4), static_cast<long long>(*s * 4),
          static_cast<signed char>(*b), *l});
  *r = -2.5;
  *s = 0.5F;
  *b = -7;
  *l = -6000000000LL;
}

void ChangeScalars(svBit* b, svLogic* l, void** c) {
  SeeInC({*b, *l, *c == &HandleCell(0) ? 1 : 0});
  *b = 1;
  *l = sv_z;
  *c = &HandleCell(1);
}

TEST(DpiInoutAndOutputArguments, NumericInoutsArriveAndAreWrittenBack) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void change(inout real r,\n"
      "      inout shortreal s, inout byte b, inout longint l);\n"
      "  real r = 1.25;\n"
      "  shortreal s = 0.75;\n"
      "  byte b = -3;\n"
      "  longint l = 64'sd5000000000;\n"
      "  bit ok;\n"
      "  initial begin\n"
      "    change(r, s, b, l);\n"
      "    ok = r == -2.5 && s == 0.5 && b == -7 && l == -64'sd6000000000;\n"
      "  end\n",
      f, {{"change", CAddress(&ChangeNumbers)}},
      "annex_h_08_08_numeric_inouts");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{5, 3, -3, 5000000000LL}));
  EXPECT_EQ(DesignValue(f, "ok"), 1U);
}

TEST(DpiInoutAndOutputArguments, ScalarAndHandleInoutsArriveAndAreWrittenBack) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void change(inout bit b, inout logic l,\n"
      "      inout chandle c);\n"
      "  import \"DPI-C\" function chandle first_handle();\n"
      "  import \"DPI-C\" function int is_second(input chandle c);\n"
      "  bit b = 0;\n"
      "  logic l = 1'bx;\n"
      "  chandle c;\n"
      "  bit ok_l;\n"
      "  int second;\n"
      "  initial begin\n"
      "    c = first_handle();\n"
      "    change(b, l, c);\n"
      "    ok_l = l === 1'bz;\n"
      "    second = is_second(c);\n"
      "  end\n",
      f,
      {{"change", CAddress(&ChangeScalars)},
       {"first_handle", CAddress(&FirstHandle)},
       {"is_second", CAddress(&HandleIsSecond)}},
      "annex_h_08_08_scalar_inouts");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0, sv_x, 1}));
  EXPECT_EQ(DesignValue(f, "b"), 1U);
  EXPECT_EQ(DesignValue(f, "ok_l"), 1U);
  EXPECT_EQ(DesignValue(f, "second"), 1U);
}

struct SmallRecord {
  int x;
  short y;
};

void ChangeAggregates(SmallRecord* s, int* a) {
  SeeInC({s->x, s->y, a[0], a[1], a[2]});
  s->x = 11;
  s->y = -12;
  a[0] = 21;
  a[2] = 23;
}

TEST(DpiInoutAndOutputArguments, AggregateInoutsArriveAndAreCopiedBack) {
  SimFixture f;
  RunModuleWithC(
      "  typedef struct { int x; shortint y; } record;\n"
      "  import \"DPI-C\" function void change(inout record s,\n"
      "      inout int a[3]);\n"
      "  record s;\n"
      "  int a[3] = '{4, 5, 6};\n"
      "  bit ok_s;\n"
      "  initial begin\n"
      "    s.x = 70000; s.y = -2;\n"
      "    change(s, a);\n"
      "    ok_s = s.x == 11 && s.y == -12;\n"
      "  end\n",
      f, {{"change", CAddress(&ChangeAggregates)}},
      "annex_h_08_08_aggregate_inouts");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{70000, -2, 4, 5, 6}));
  EXPECT_EQ(DesignValue(f, "ok_s"), 1U);
  EXPECT_EQ(DesignValue(f, "a[0]"), 21U);
  EXPECT_EQ(DesignValue(f, "a[1]"), 5U);
  EXPECT_EQ(DesignValue(f, "a[2]"), 23U);
}

}  // namespace
