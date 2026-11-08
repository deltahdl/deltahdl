#include <gtest/gtest.h>

#include <map>
#include <string>
#include <type_traits>
#include <vector>

#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(DpiCFunctionResult, TheResultTypesAreTheTenTheClauseLists) {
  const std::vector<DataTypeKind> kExpected = {
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kReal,     DataTypeKind::kShortreal,
      DataTypeKind::kChandle, DataTypeKind::kString,   DataTypeKind::kBit,
      DataTypeKind::kLogic};
  EXPECT_EQ(DpiResultTypes(), kExpected);
  for (const DataTypeKind kKind : DpiResultTypes()) {
    EXPECT_TRUE(DpiTypeMayBeAResult(kKind));
    EXPECT_FALSE(DpiCTypeOfResult(kKind).empty());
  }
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kInteger));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kTime));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kStruct));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kEvent));
}

TEST(DpiCFunctionResult, EachResultIsReturnedAsItsTableType) {
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kByte), "char");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kShortint), "short int");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kLongint), "long long");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kShortreal), "float");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kChandle), "void*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kString), "const char*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kBit), "svBit");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kLogic), "svLogic");
  EXPECT_TRUE((std::is_same<svBit, unsigned char>::value));
  EXPECT_TRUE((std::is_same<svLogic, unsigned char>::value));
  const svLogic kCodes[] = {sv_0, sv_1, sv_z, sv_x};
  EXPECT_EQ(kCodes[0], 0);
  EXPECT_EQ(kCodes[3], 3);
}

char ReturnByte() { return -100; }
short ReturnShortint() { return -30000; }
int ReturnInt() { return 70000; }
long long ReturnLongint() { return 5000000000LL; }
double ReturnReal() { return 2.5; }
float ReturnShortreal() { return 0.75F; }
int result_cell = 0;
void* ReturnChandle() { return &result_cell; }
unsigned char ReturnBit() { return 1; }
unsigned char ReturnLogic() { return 3; }
int void_calls = 0;
void ReturnNothing() { ++void_calls; }
int ReturnFromTask() {
  ++void_calls;
  return 0;
}

TEST(DpiCFunctionResult, EachResultComesBackAsItsDeclaredType) {
  const std::map<std::string, DataTypeKind> kResults = {
      {"return_byte", DataTypeKind::kByte},
      {"return_shortint", DataTypeKind::kShortint},
      {"return_int", DataTypeKind::kInt},
      {"return_longint", DataTypeKind::kLongint},
      {"return_real", DataTypeKind::kReal},
      {"return_shortreal", DataTypeKind::kShortreal},
      {"return_chandle", DataTypeKind::kChandle},
      {"return_bit", DataTypeKind::kBit},
      {"return_logic", DataTypeKind::kLogic},
      {"return_nothing", DataTypeKind::kVoid}};
  DpiCBinding b;
  for (const auto& [name, result] : kResults) {
    b.dpi.RegisterImport(CImport(name, result, {}));
  }
  DpiRtFunction task = CImport("return_from_task", DataTypeKind::kVoid, {});
  task.is_task = true;
  b.dpi.RegisterImport(task);
  b.Bind({{"return_byte", reinterpret_cast<void*>(&ReturnByte)},
          {"return_shortint", reinterpret_cast<void*>(&ReturnShortint)},
          {"return_int", reinterpret_cast<void*>(&ReturnInt)},
          {"return_longint", reinterpret_cast<void*>(&ReturnLongint)},
          {"return_real", reinterpret_cast<void*>(&ReturnReal)},
          {"return_shortreal", reinterpret_cast<void*>(&ReturnShortreal)},
          {"return_chandle", reinterpret_cast<void*>(&ReturnChandle)},
          {"return_bit", reinterpret_cast<void*>(&ReturnBit)},
          {"return_logic", reinterpret_cast<void*>(&ReturnLogic)},
          {"return_nothing", reinterpret_cast<void*>(&ReturnNothing)},
          {"return_from_task", reinterpret_cast<void*>(&ReturnFromTask)}},
         "annex_h_08_09_results");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> none;
  const DpiArgValue kByte = b.Call("return_byte", none);
  EXPECT_EQ(kByte.type, DataTypeKind::kByte);
  EXPECT_EQ(kByte.AsInt(), -100);
  EXPECT_EQ(b.Call("return_shortint", none).AsInt(), -30000);
  EXPECT_EQ(b.Call("return_int", none).AsInt(), 70000);
  EXPECT_EQ(b.Call("return_longint", none).AsLongint(), 5000000000LL);
  EXPECT_DOUBLE_EQ(b.Call("return_real", none).AsReal(), 2.5);
  const DpiArgValue kShortreal = b.Call("return_shortreal", none);
  EXPECT_EQ(kShortreal.type, DataTypeKind::kShortreal);
  EXPECT_DOUBLE_EQ(kShortreal.AsReal(), 0.75);
  EXPECT_EQ(b.Call("return_chandle", none).AsChandle(), &result_cell);
  EXPECT_EQ(b.Call("return_bit", none).AsBit(), 1);
  EXPECT_EQ(b.Call("return_logic", none).AsLogic(), 3);
  b.Call("return_nothing", none);
  b.Call("return_from_task", none);
  EXPECT_EQ(void_calls, 2);
}

}  // namespace
