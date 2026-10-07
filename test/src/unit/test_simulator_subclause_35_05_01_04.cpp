#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// §35.5.1.4 "Memory management". The foreign code and the SystemVerilog code
// own and allocate separate memory, and each side looks after its own: an
// imported function must not free memory SystemVerilog or its compiler
// allocated, nor count on SystemVerilog freeing memory the foreign code or its
// compiler allocated.
//
// Those two sentences bind the author of the foreign code, not the tool: a
// simulator cannot stop a C function calling free on a pointer it was not
// given. What the clause asks of the tool is in the sentence after them, which
// describes the one arrangement by which a block does cross: foreign code may
// allocate a block, hand SystemVerilog a pointer to it, and have SystemVerilog
// later call an imported function, C's free for one, that frees the block,
// directly or not. SystemVerilog holds the handle and never the block, so the
// handle has to reach the freeing import as the address the allocating one
// returned. A boundary that altered it would have the second import free
// something the first never allocated, which the NOTE rules out by saying that
// in this scenario the block is both allocated and freed on the foreign side
// whatever SystemVerilog did in between.
//
// §35.5.6 admits chandle as a formal argument type and §35.5.5 as a result
// type, so the handle is a chandle at both ends.
namespace {

// §35.5.1.4: the block is allocated in foreign code, its handle is returned to
// SystemVerilog as a chandle, SystemVerilog hands that chandle to a second
// import, and that import frees the block. The address the second import is
// given is the address the first one returned, so the block freed is the block
// allocated.
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
    // Free only the block this case allocated. A handle the boundary had
    // altered would not address a block anything allocated, and freeing it
    // would be undefined behaviour rather than a failed assertion.
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

// §35.5.1.4: the handle is a pointer, and a pointer is wider than the integer
// types a DPI argument is otherwise carried as. This hands the boundary an
// address whose upper half is set and never dereferences it, so the case says
// what happens to the value and nothing about the memory: an argument coerced
// through a 32-bit integer arrives with its upper half gone, and the import
// that freed it in the case above would then free an address the allocating
// one never returned.
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

  // Never dereferenced. The low half alone is 0x9ABCDEF0, which the whole
  // value is not, so a truncating crossing is visible in the assertion.
  auto* const kAddress = reinterpret_cast<void*>(0x123456789ABCDEF0ULL);
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromChandle(kAddress)};
  rt.CallImportWithArgs("sv_take", actuals);

  EXPECT_EQ(seen, kAddress);
}

}  // namespace
