#include <gtest/gtest.h>

#include <cstdint>
#include <string>
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

TEST(DpiInputArguments, TheForeignCodeMayNotModifyAnInput) {
  EXPECT_FALSE(DpiForeignCodeMayModifyFormal(Direction::kInput));
  EXPECT_TRUE(DpiForeignCodeMayModifyFormal(Direction::kOutput));
  EXPECT_TRUE(DpiForeignCodeMayModifyFormal(Direction::kInout));
}

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
  EXPECT_EQ(static_cast<uint32_t>(kResult.AsInt()), 0x9ABCDEF0U);
  ASSERT_TRUE(actuals[0].IsWideVec());
  EXPECT_EQ(actuals[0].AsLogicVecWords()[0].aval, 0x12345678U);
  EXPECT_EQ(actuals[0].AsLogicVecWords()[1].aval, 0x9ABCDEF0U);
}

void OverwriteBits(const svBitVecVal* v) {
  auto* writable = const_cast<svBitVecVal*>(v);
  writable[0] = 0xFFFFFFFFU;
  writable[1] = 0xFFFFFFFFU;
}

void OverwriteLogic(const svLogicVecVal* v) {
  auto* writable = const_cast<svLogicVecVal*>(v);
  writable[0] = {0xFFFFFFFFU, 0U};
  writable[1] = {0xFFFFFFFFU, 0U};
}

void OverwriteString(const char* s) { const_cast<char*>(s)[0] = 'X'; }

void OverwriteOpenArray(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    *static_cast<int*>(svGetArrElemPtr1(h, i)) = -1;
  }
}

TEST(DpiInputArguments, AWriteToAWidePackedInputLeavesTheDesignsActual) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function void over_bits(input bit [63:0] v);\n"
      "  import \"DPI-C\" function void over_logic(input logic [63:0] v);\n"
      "  bit [63:0] b = 64'h1234_5678_9abc_def0;\n"
      "  logic [63:0] l = 64'h0fed_cba9_8765_4321;\n"
      "  initial begin over_bits(b); over_logic(l); end\n"
      "endmodule\n",
      f,
      {{"over_bits", reinterpret_cast<void*>(&OverwriteBits)},
       {"over_logic", reinterpret_cast<void*>(&OverwriteLogic)}},
      "annex_h_06_02_packed");
  EXPECT_EQ(DesignValue(f, "b"), 0x123456789ABCDEF0U);
  EXPECT_EQ(DesignValue(f, "l"), 0x0FEDCBA987654321U);
}

TEST(DpiInputArguments, AWriteToAStringInputLeavesTheDesignsActual) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function void over_string(input string s);\n"
      "  string s = \"abc\";\n"
      "  bit kept;\n"
      "  initial begin over_string(s); kept = s == \"abc\"; end\n"
      "endmodule\n",
      f, {{"over_string", reinterpret_cast<void*>(&OverwriteString)}},
      "annex_h_06_02_string");
  EXPECT_EQ(DesignValue(f, "kept"), 1U);
}

TEST(DpiInputArguments, AWriteToAnOpenArrayInputLeavesTheDesignsActual) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function void over_array(input int a []);\n"
      "  int a [2:3] = '{20, 30};\n"
      "  initial over_array(a);\n"
      "endmodule\n",
      f, {{"over_array", reinterpret_cast<void*>(&OverwriteOpenArray)}},
      "annex_h_06_02_open_array");
  EXPECT_EQ(DesignValue(f, "a[2]"), 20U);
  EXPECT_EQ(DesignValue(f, "a[3]"), 30U);
}

}  // namespace
