#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
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

struct Block {
  int allocations = 0;
  int frees = 0;
  void* allocated = nullptr;
  void* freed = nullptr;
};

Block& TheBlock() {
  static Block block;
  return block;
}

void* AllocateBlock() {
  ++TheBlock().allocations;
  TheBlock().allocated = new int(7);
  return TheBlock().allocated;
}

int ReadBlock(void* handle) {
  return handle == TheBlock().allocated ? *static_cast<int*>(handle) : -1;
}

void FreeBlock(void* handle) {
  ++TheBlock().frees;
  TheBlock().freed = handle;
  delete static_cast<int*>(handle);
}

TEST(DpiMemorySpaces, ADesignsChandleCarriesABlockFromItsAllocationToItsFree) {
  TheBlock() = Block{};
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function chandle c_alloc();\n"
      "  import \"DPI-C\" function int c_read(input chandle h);\n"
      "  import \"DPI-C\" function void c_free(input chandle h);\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial begin\n"
      "    h = c_alloc();\n"
      "    #5 r = c_read(h);\n"
      "    c_free(h);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"c_alloc", reinterpret_cast<void*>(&AllocateBlock)},
       {"c_read", reinterpret_cast<void*>(&ReadBlock)},
       {"c_free", reinterpret_cast<void*>(&FreeBlock)}},
      "annex_h_06_06_chandle");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(TheBlock().allocations, 1);
  EXPECT_EQ(TheBlock().frees, 1);
  EXPECT_EQ(TheBlock().freed, TheBlock().allocated);
  EXPECT_EQ(DesignValue(f, "r"), 7U);
}

}  // namespace
