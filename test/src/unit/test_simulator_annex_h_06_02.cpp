#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.6.2 (Input arguments): a formal specified in SystemVerilog as
// input shall not be modified by the foreign language code, as §35.5.1.2
// has it. The cases check which directions the foreign code may modify,
// that the C type of every input carries const to say so however the input
// is passed, and that a modification the foreign code makes to a packed
// input, which crosses by reference to its canonical form, does not reach
// the actual.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.6.2: the foreign code may modify an output or an inout formal and
// never an input.
TEST(DpiInputArguments, TheForeignCodeMayNotModifyAnInput) {
  EXPECT_FALSE(DpiForeignCodeMayModifyFormal(Direction::kInput));
  EXPECT_TRUE(DpiForeignCodeMayModifyFormal(Direction::kOutput));
  EXPECT_TRUE(DpiForeignCodeMayModifyFormal(Direction::kInout));
}

// §H.6.2 as the C layer states it: the C type of an input carries the
// const qualifier whether the input is passed by value, by reference to
// its canonical form, as a string, or by open array handle, where an output
// or inout of the same type does not.
TEST(DpiInputArguments, AnInputsCTypeIsConstHoweverItIsPassed) {
  const std::string kByValue =
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), false);
  EXPECT_TRUE(kByValue.starts_with("const ")) << kByValue;
  const std::string kByReference = DpiCTypeOfFormal(
      Formal(DataTypeKind::kBit, Direction::kInput, 64), false);
  EXPECT_TRUE(kByReference.starts_with("const ")) << kByReference;
  const std::string kString =
      DpiCTypeOfFormal(Formal(DataTypeKind::kString, Direction::kInput), false);
  EXPECT_TRUE(kString.starts_with("const ")) << kString;
  const std::string kOpenArray =
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kInput, 8), true);
  EXPECT_TRUE(kOpenArray.starts_with("const ")) << kOpenArray;
  EXPECT_FALSE(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), false)
          .starts_with("const "));
  EXPECT_FALSE(
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kInout, 64), false)
          .starts_with("const "));
}

// §H.6.2: a packed input crosses in its canonical form, and a foreign
// function that overwrites the words it was handed changes nothing the
// caller sees -- the actual `bit [63:0]` still holds what it held.
TEST(DpiInputArguments, AModificationOfAPackedInputDoesNotReachTheActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_scan";
  func.sv_name = "scan";
  func.return_type = DataTypeKind::kInt;
  DpiArg formal = Formal(DataTypeKind::kBit, Direction::kInput, 64);
  formal.name = "v";
  func.args = {formal};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    const uint32_t kSeen = a[0].AsLogicVecWords()[1].aval;
    a[0] = DpiArgValue::FromLogicVecWords(
        {SvLogicVecVal{0xFFFFFFFFU, 0U}, SvLogicVecVal{0xFFFFFFFFU, 0U}}, 64,
        DataTypeKind::kBit);
    return DpiArgValue::FromInt(static_cast<int32_t>(kSeen));
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLogicVecWords(
      {SvLogicVecVal{0x12345678U, 0U}, SvLogicVecVal{0x9ABCDEF0U, 0U}}, 64,
      DataTypeKind::kBit)};
  const DpiArgValue kResult = rt.CallImportWithArgs("scan", actuals);
  // The foreign function read the input's upper word...
  EXPECT_EQ(static_cast<uint32_t>(kResult.AsInt()), 0x9ABCDEF0U);
  // ...and its overwrite went nowhere.
  ASSERT_TRUE(actuals[0].IsWideVec());
  EXPECT_EQ(actuals[0].AsLogicVecWords()[0].aval, 0x12345678U);
  EXPECT_EQ(actuals[0].AsLogicVecWords()[1].aval, 0x9ABCDEF0U);
}

}  // namespace
