#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiMemoryManagement, AHandleReachesTheImportThatFreesTheBlockUnchanged) {
  DpiRuntime rt;

  DpiRtFunction alloc;
  alloc.c_name = "c_alloc";
  alloc.sv_name = "sv_alloc";
  alloc.return_type = DataTypeKind::kChandle;
  alloc.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromChandle(new int32_t(0x5A5A));
  };
  rt.RegisterImport(alloc);

  void* handed_back = nullptr;
  int32_t freed_contents = 0;
  bool freed = false;
  void* allocated = nullptr;

  DpiRtFunction release;
  release.c_name = "c_release";
  release.sv_name = "sv_release";
  release.return_type = DataTypeKind::kVoid;
  release.args = {DpiArg{"h", DataTypeKind::kChandle, Direction::kInput}};
  release.impl = [&](const std::vector<DpiArgValue>& args) {
    handed_back = args[0].AsChandle();
    if (handed_back == allocated) {
      freed_contents = *static_cast<int32_t*>(handed_back);
      delete static_cast<int32_t*>(handed_back);
      freed = true;
    }
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(release);

  const DpiArgValue kHandle = rt.CallImport("sv_alloc", {});
  allocated = kHandle.AsChandle();
  std::vector<DpiArgValue> actuals = {kHandle};
  rt.CallImportWithArgs("sv_release", actuals);

  EXPECT_EQ(handed_back, allocated);
  EXPECT_TRUE(freed);
  EXPECT_EQ(freed_contents, 0x5A5A);
}

TEST(DpiMemoryManagement, AHandleWiderThanAnIntCrossesWithItsUpperHalfIntact) {
  DpiRuntime rt;

  void* seen = nullptr;
  DpiRtFunction take;
  take.c_name = "c_take";
  take.sv_name = "sv_take";
  take.return_type = DataTypeKind::kVoid;
  take.args = {DpiArg{"h", DataTypeKind::kChandle, Direction::kInput}};
  take.impl = [&seen](const std::vector<DpiArgValue>& args) {
    seen = args[0].AsChandle();
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(take);

  auto* const kAddress = reinterpret_cast<void*>(0x123456789ABCDEF0ULL);
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromChandle(kAddress)};
  rt.CallImportWithArgs("sv_take", actuals);

  EXPECT_EQ(seen, kAddress);
}

}  // namespace
