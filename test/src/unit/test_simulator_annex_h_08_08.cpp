#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "parser/ast.h"
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

}  // namespace
