#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.8.8 (Inout and output arguments): an inout or output argument,
// open arrays excepted, is always passed by reference, a packed array as
// svBitVecVal* or svLogicVecVal*, and the same rules about unused bits
// apply as in §H.7.7. The cases check the mode and C type an output or
// inout takes and that the unused bits of a packed output's last chunk are
// what the foreign code left there, the value being the bits within the
// width once masked as §H.7.7 has the user do.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.8: an output or inout of any type but an open array is passed by
// reference -- an int as int*, a packed bit array as svBitVecVal*, a packed
// logic array, an integer and a time as svLogicVecVal* -- and an open array
// stays the handle.
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

// §H.8.8 with §H.7.7: the unused bits of the last chunk a foreign function
// writes to a `bit [7:0]` output are undetermined, so the chunk comes back
// holding whatever it left there and the value is the eight bits within
// the width once masked -- 0xAB out of 0xFFFFFFAB.
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

// The C functions the imports below are bound to, each writing its output and
// inout formals through the pointers they arrive as.
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

// §H.8.8: an output or inout of a small type is passed by reference, a pointer
// to its C type, and what the C function leaves there becomes the formal's
// value on return (§35.5.1.2); an inout arrives holding the actual's value.
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

// §H.8.8: a packed output is passed as svBitVecVal* or svLogicVecVal*, and the
// §H.7.7 rule about unused bits applies: what lies beyond the width in the
// last chunk is undetermined, and the value is what lies within it. An
// integer is one aval/bval pair and a time two.
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
  EXPECT_EQ(args[3].AsLongint(), (2LL << 32) | 5);
}

}  // namespace
