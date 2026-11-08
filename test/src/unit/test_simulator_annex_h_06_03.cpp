#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiOutputArguments, AnOutputsInitialValueIsUndetermined) {
  EXPECT_TRUE(DpiFormalIsDeterminedOnEntry(Direction::kInput));
  EXPECT_TRUE(DpiFormalIsDeterminedOnEntry(Direction::kInout));
  EXPECT_FALSE(DpiFormalIsDeterminedOnEntry(Direction::kOutput));
}

TEST(DpiOutputArguments, APackedOutputDoesNotCarryTheActualIn) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_fill";
  func.sv_name = "fill";
  func.return_type = DataTypeKind::kInt;
  DpiArg formal;
  formal.name = "v";
  formal.type = DataTypeKind::kBit;
  formal.direction = Direction::kOutput;
  formal.width = 64;
  func.args = {formal};
  uint32_t seen_low = 0;
  uint32_t seen_high = 0;
  func.arg_impl = [&](std::vector<DpiArgValue>& a) {
    seen_low = a[0].IsWideVec() ? a[0].AsLogicVecWords()[0].aval : 0;
    seen_high = a[0].IsWideVec() ? a[0].AsLogicVecWords()[1].aval : 0;
    a[0] = DpiArgValue::FromLogicVecWords(
        {SvLogicVecVal{0x11111111U, 0U}, SvLogicVecVal{0x22222222U, 0U}}, 64,
        DataTypeKind::kBit);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLogicVecWords(
      {SvLogicVecVal{0x12345678U, 0U}, SvLogicVecVal{0x9ABCDEF0U, 0U}}, 64,
      DataTypeKind::kBit)};
  rt.CallImportWithArgs("fill", actuals);
  EXPECT_NE(seen_low, 0x12345678U);
  EXPECT_NE(seen_high, 0x9ABCDEF0U);
  ASSERT_TRUE(actuals[0].IsWideVec());
  EXPECT_EQ(actuals[0].AsLogicVecWords()[0].aval, 0x11111111U);
  EXPECT_EQ(actuals[0].AsLogicVecWords()[1].aval, 0x22222222U);
}

}  // namespace
