#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.6.6 (Memory management), beside §35.5.1.4: the memory spaces C
// code and SystemVerilog code own and allocate are disjoint and each side is
// responsible for its own -- C shall not free memory SystemVerilog or its
// compiler allocated, nor expect SystemVerilog to free memory C or its
// compiler allocated -- which does not exclude C allocating a block and
// passing a handle to it to SystemVerilog, which in turn calls a C function
// that frees the block, directly if it is free itself or indirectly; in
// that scenario the block is allocated and freed in C even where malloc and
// free are called directly from SystemVerilog. The cases check that a side
// may free only what it allocated, and that a block behind a chandle is C's
// and an imported call is C's work, so that freeing it through an import
// is C freeing its own.

namespace {

// §H.6.6: each side frees what it allocated and nothing the other did.
TEST(DpiMemorySpaces, EachSideFreesOnlyWhatItAllocated) {
  EXPECT_TRUE(DpiSideMayFree(DpiMemorySide::kC, DpiMemorySide::kC));
  EXPECT_TRUE(DpiSideMayFree(DpiMemorySide::kSystemVerilog,
                             DpiMemorySide::kSystemVerilog));
  EXPECT_FALSE(
      DpiSideMayFree(DpiMemorySide::kSystemVerilog, DpiMemorySide::kC));
  EXPECT_FALSE(
      DpiSideMayFree(DpiMemorySide::kC, DpiMemorySide::kSystemVerilog));
}

// §H.6.6: the block a chandle refers to is C's, SystemVerilog holding the
// handle and never the block, and a call of an imported function is C's
// work whatever SystemVerilog code made it -- so a release through an
// import is C freeing what C allocated, which the runtime lets happen with
// the handle it was returned.
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
