#include <gtest/gtest.h>

#include <cstdlib>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi_sv31a.h"

using namespace delta;

namespace {

// §H.14.6, the C side of Example 11, compiled against svdpi.h and its SV3.1a
// companion alone -- svdpi_src.h is not needed -- under the name MyFunc
// this tree's naming rules give the example's myfunc: the exported function
// takes an svLogicPackedArrRef, and the C code allocates the simulator's
// representation of a 32-bit logic array dynamically by its size, calls the
// export with the reference, reads the result back into a canonical buffer
// and frees the block, using the canonical representation alone from then
// on.

// What the example's SystemVerilog function does is elided; this stand-in
// writes a value into the output's actual representation through the
// reference.
void MyFunc(svLogicPackedArrRef r) {
  const svLogicVec32 kValue = {0xC0FFEE42u, 0x0000000Fu};
  svPutLogicVec32(r, &kValue, 32);
}

// §H.14.6: an application allocating the representation dynamically needs
// no svdpi_src.h and so stays binary compatible.
TEST(DpiBinaryCompatibleExportCall, DynamicAllocationNeedsNoSvdpiSrc) {
  EXPECT_FALSE(DpiSvdpiSrcIsNeededForExportCall(true));
  EXPECT_TRUE(DpiSvdpiSrcIsNeededForExportCall(false));
  EXPECT_EQ(DpiCompatibilityOfApplication(false),
            DpiApplicationCompatibility::kBinary);
}

// The example run: the block malloc gives for svSizeOfLogicPackedArr(32) is
// the reference the export writes through, the canonical copy read back from
// it carries the c and d words the export put, and the block is freed.
TEST(DpiBinaryCompatibleExportCall, TheExportWritesTheAllocatedRepresentation) {
  /* output logic packed 32-bits */
  svLogicVec32 my_r[SV_CANONICAL_SIZE(32)] = {};
  /* my array, canonical representation */

  /* allocate memory for logic packed 32-bits in simulator's representation */
  auto r = static_cast<svLogicPackedArrRef>(
      malloc(static_cast<size_t>(svSizeOfLogicPackedArr(32))));
  ASSERT_NE(r, nullptr);
  MyFunc(r);
  /* canonical <-- actual */
  svGetLogicVec32(my_r, r, 32);
  /* shall use only the canonical representation from now on */
  free(r); /* do not need any more */

  EXPECT_EQ(SV_CANONICAL_SIZE(32), 1);
  EXPECT_EQ(my_r[0].c, 0xC0FFEE42u);
  EXPECT_EQ(my_r[0].d, 0x0000000Fu);
}

}  // namespace
