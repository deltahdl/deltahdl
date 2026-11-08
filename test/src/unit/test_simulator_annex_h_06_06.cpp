#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiMemorySpaces, EachSideFreesOnlyWhatItAllocated) {
  EXPECT_TRUE(DpiSideMayFree(DpiMemorySide::kC, DpiMemorySide::kC));
  EXPECT_TRUE(DpiSideMayFree(DpiMemorySide::kSystemVerilog,
                             DpiMemorySide::kSystemVerilog));
  EXPECT_FALSE(
      DpiSideMayFree(DpiMemorySide::kSystemVerilog, DpiMemorySide::kC));
  EXPECT_FALSE(
      DpiSideMayFree(DpiMemorySide::kC, DpiMemorySide::kSystemVerilog));
}

TEST(DpiMemorySpaces, ABlockBehindAChandleIsFreedInCThroughAnImport) {
  EXPECT_EQ(DpiSideOwningBlockBehindChandle(), DpiMemorySide::kC);
  EXPECT_EQ(DpiSideOfImportedCall(), DpiMemorySide::kC);
  EXPECT_TRUE(DpiSideMayFree(DpiSideOwningBlockBehindChandle(),
                             DpiSideOfImportedCall()));

  DpiRuntime rt;
  DpiRtFunction acquire;
  acquire.c_name = "c_acquire";
  acquire.sv_name = "acquire";
  acquire.return_type = DataTypeKind::kChandle;
  acquire.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromChandle(new int32_t(7));
  };
  rt.RegisterImport(acquire);
  void* released = nullptr;
  DpiRtFunction release;
  release.c_name = "c_release";
  release.sv_name = "release";
  release.return_type = DataTypeKind::kVoid;
  release.args = {DpiArg{"h", DataTypeKind::kChandle, Direction::kInput}};
  release.impl = [&released](const std::vector<DpiArgValue>& args) {
    released = args[0].AsChandle();
    delete static_cast<int32_t*>(released);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(release);

  const DpiArgValue kHandle = rt.CallImport("acquire", {});
  rt.CallImport("release", {kHandle});
  EXPECT_EQ(released, kHandle.AsChandle());
}

}  // namespace
