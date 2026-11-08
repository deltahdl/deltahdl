#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

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

TEST(DpiPassingByValue, OnlyASmallInputIsPassedByValue) {
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kInput), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kReal, Direction::kInput), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kLogic, Direction::kInput, 1), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kChandle, Direction::kInput), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kString, Direction::kInput), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kOutput), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kInout), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kBit, Direction::kInput, 8), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kInput), true));
}

TEST(DpiPassingByValue, TheUserProvidesTheEquivalentCType) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), false),
      "const int");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kReal, Direction::kInput), false),
      "const double");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kLogic, Direction::kInput, 1),
                             false),
            "const svLogic");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kString, Direction::kInput), false),
      "const char*");
}

TEST(DpiPassingByValue, TheResultIsReturnedByValueAsItsCType) {
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kInt), "int");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kReal), "double");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kBit), "svBit");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kString), "const char*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kChandle), "void*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kVoid), "void");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kInteger), "");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kStruct), "");
}

long long SumByValue(char b, short s, int i, long long l) {
  return b + s + i + l;
}

long long SumUnsignedByValue(unsigned char b, unsigned short s,
                             unsigned int i) {
  return static_cast<long long>(b) + s + i;
}

double RealsByValue(double r, float f) { return (r * 10) + f; }

int ScalarsAndHandleByValue(unsigned char bit, unsigned char logic,
                            const void* handle) {
  return (bit * 100) + (logic * 10) + *static_cast<const int*>(handle);
}

TEST(DpiPassingByValue, EachSmallInputArrivesAsItsOwnCType) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("sum_by_value", DataTypeKind::kLongint,
              {CFormal("b", DataTypeKind::kByte, Direction::kInput),
               CFormal("s", DataTypeKind::kShortint, Direction::kInput),
               CFormal("i", DataTypeKind::kInt, Direction::kInput),
               CFormal("l", DataTypeKind::kLongint, Direction::kInput)}));
  DpiArg ub = CFormal("b", DataTypeKind::kByte, Direction::kInput);
  DpiArg us = CFormal("s", DataTypeKind::kShortint, Direction::kInput);
  DpiArg ui = CFormal("i", DataTypeKind::kInt, Direction::kInput);
  ub.is_unsigned = us.is_unsigned = ui.is_unsigned = true;
  b.dpi.RegisterImport(
      CImport("sum_unsigned_by_value", DataTypeKind::kLongint, {ub, us, ui}));
  b.Bind(
      {{"sum_by_value", reinterpret_cast<void*>(&SumByValue)},
       {"sum_unsigned_by_value", reinterpret_cast<void*>(&SumUnsignedByValue)}},
      "annex_h_08_03_integers");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> args = {
      DpiArgValue::FromInt(-3), DpiArgValue::FromInt(-300),
      DpiArgValue::FromInt(70000), DpiArgValue::FromLongint(5000000000LL)};
  EXPECT_EQ(b.Call("sum_by_value", args).AsLongint(), 5000069697LL);
  std::vector<DpiArgValue> unsigned_args = {
      DpiArgValue::FromInt(255), DpiArgValue::FromInt(65535),
      DpiArgValue::FromInt(static_cast<int32_t>(4294967040U))};
  EXPECT_EQ(b.Call("sum_unsigned_by_value", unsigned_args).AsLongint(),
            4295032830LL);
}

TEST(DpiPassingByValue, RealsScalarsAndHandlesArriveAsTheirCTypes) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("reals_by_value", DataTypeKind::kReal,
              {CFormal("r", DataTypeKind::kReal, Direction::kInput),
               CFormal("f", DataTypeKind::kShortreal, Direction::kInput)}));
  b.dpi.RegisterImport(
      CImport("scalars_by_value", DataTypeKind::kInt,
              {CFormal("bit", DataTypeKind::kBit, Direction::kInput),
               CFormal("logic", DataTypeKind::kLogic, Direction::kInput),
               CFormal("handle", DataTypeKind::kChandle, Direction::kInput)}));
  b.Bind(
      {{"reals_by_value", reinterpret_cast<void*>(&RealsByValue)},
       {"scalars_by_value", reinterpret_cast<void*>(&ScalarsAndHandleByValue)}},
      "annex_h_08_03_reals");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> reals = {DpiArgValue::FromReal(2.5),
                                    DpiArgValue::FromReal(0.25)};
  reals[1].type = DataTypeKind::kShortreal;
  EXPECT_DOUBLE_EQ(b.Call("reals_by_value", reals).AsReal(), 25.25);
  int cell = 7;
  std::vector<DpiArgValue> scalars = {DpiArgValue::FromBit(1),
                                      DpiArgValue::FromLogic(3),
                                      DpiArgValue::FromChandle(&cell)};
  EXPECT_EQ(b.Call("scalars_by_value", scalars).AsInt(), 137);
}

double RealtimeAndRegByValue(double r, unsigned char g) { return r + (g * 10); }

TEST(DpiPassingByValue, ARealtimeAndARegArriveAsDoubleAndSvLogic) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("realtime_and_reg", DataTypeKind::kReal,
              {CFormal("r", DataTypeKind::kRealtime, Direction::kInput),
               CFormal("g", DataTypeKind::kReg, Direction::kInput)}));
  b.Bind(
      {{"realtime_and_reg", reinterpret_cast<void*>(&RealtimeAndRegByValue)}},
      "annex_h_08_03_realtime_reg");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  DpiArgValue realtime = DpiArgValue::FromReal(1.5);
  realtime.type = DataTypeKind::kRealtime;
  DpiArgValue reg = DpiArgValue::FromLogic(3);
  reg.type = DataTypeKind::kReg;
  std::vector<DpiArgValue> args = {realtime, reg};
  EXPECT_DOUBLE_EQ(b.Call("realtime_and_reg", args).AsReal(), 31.5);
}

}  // namespace
