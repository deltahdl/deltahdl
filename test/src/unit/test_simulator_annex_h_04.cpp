#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <type_traits>

// Annex H.4 (Portability) makes a single normative promise: DPI object code
// compiled on a platform works with every SystemVerilog simulator on that
// platform. What makes that promise hold is the shape of the interface the DPI
// C layer carries in svdpi.h -- it is expressed entirely in platform-stable,
// exact-width data so that code compiled against the header has one fixed
// binary representation on a given platform regardless of which simulator
// implements it. These tests include the production header directly and
// observe that the types it defines actually carry that fixed, portable
// representation. svdpi.h is included alone: it intentionally redefines a few
// VPI names, so it must not share a translation unit with vpi.h.
#include "simulator/svdpi.h"

namespace delta {
namespace {

// §H.4: the scalar interface types are exact-width single-byte unsigned
// integers. A one-byte unsigned representation is identical on every platform,
// so object code that passes an svBit/svLogic/svScalar agrees on its layout
// with any simulator built from the same header.
TEST(SvdpiPortability, ScalarTypesHaveFixedSingleByteRepresentation) {
  EXPECT_EQ(sizeof(svScalar), 1u);
  EXPECT_EQ(sizeof(svBit), 1u);
  EXPECT_EQ(sizeof(svLogic), 1u);

  EXPECT_TRUE(std::is_unsigned<svScalar>::value);
  EXPECT_TRUE(std::is_unsigned<svBit>::value);
  EXPECT_TRUE(std::is_unsigned<svLogic>::value);

  // Exactly eight value bits -- no platform-dependent padding or width.
  EXPECT_EQ(std::numeric_limits<svScalar>::digits, 8);

  // The four scalar codes all fit in that fixed-width scalar type, so a value
  // crossing the boundary carries the same byte on either side.
  EXPECT_EQ(static_cast<svScalar>(sv_0), 0);
  EXPECT_EQ(static_cast<svScalar>(sv_1), 1);
  EXPECT_EQ(static_cast<svScalar>(sv_z), 2);
  EXPECT_EQ(static_cast<svScalar>(sv_x), 3);
}

// §H.4: the 2-state vector word is a fixed 32-bit unsigned quantity. Packed
// bit data is exchanged as arrays of this word, so a fixed 32-bit element is
// what lets such an array round-trip through object code unchanged.
TEST(SvdpiPortability, BitVectorWordIsFixedThirtyTwoBits) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_TRUE(std::is_unsigned<svBitVecVal>::value);
  EXPECT_EQ(std::numeric_limits<svBitVecVal>::digits, 32);

  // It is the exact-width uint32_t, the same type on any conforming platform.
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
}

// §H.4: the 4-state vector word has a fixed layout -- two 32-bit fields, aval
// first then bval, eight bytes total with no reordering or padding. That fixed
// layout is what lets a 4-state value compiled into object code be read back
// identically by any simulator.
TEST(SvdpiPortability, LogicVectorWordHasFixedTwoWordLayout) {
  EXPECT_EQ(sizeof(s_vpi_vecval), 8u);
  EXPECT_EQ(offsetof(s_vpi_vecval, aval), 0u);
  EXPECT_EQ(offsetof(s_vpi_vecval, bval), 4u);
  EXPECT_EQ(sizeof(reinterpret_cast<s_vpi_vecval*>(0)->aval), 4u);
  EXPECT_EQ(sizeof(reinterpret_cast<s_vpi_vecval*>(0)->bval), 4u);

  // The DPI 4-state word is exactly that VPI vector word, so the two layers
  // share one binary representation.
  EXPECT_TRUE((std::is_same<svLogicVecVal, s_vpi_vecval>::value));
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

// §H.4: SystemVerilog-specific objects are passed across the boundary as opaque
// handles, defined as plain data pointers. A handle is therefore pointer-sized
// and carries no implementation-specific structure into object code, so any
// simulator can interpret it on its own side.
TEST(SvdpiPortability, HandlesAreOpaquePointerSized) {
  EXPECT_EQ(sizeof(svScope), sizeof(void*));
  EXPECT_EQ(sizeof(svOpenArrayHandle), sizeof(void*));

  EXPECT_TRUE(std::is_pointer<svScope>::value);
  EXPECT_TRUE(std::is_pointer<svOpenArrayHandle>::value);

  // A null handle is a valid, representation-independent value.
  svScope scope = nullptr;
  svOpenArrayHandle array = nullptr;
  EXPECT_EQ(scope, nullptr);
  EXPECT_EQ(array, nullptr);
}

// §H.4: portability across platforms relies on the header supplying the
// platform's own import/export linkage decoration. svdpi.h defines those
// decoration macros (empty on platforms with no special requirement), so the
// same interface source emits correct linkage on each platform it is compiled
// for.
TEST(SvdpiPortability, PlatformLinkageDecorationIsProvided) {
  // The header defines the import and export decoration macros unconditionally
  // (expanding to a platform attribute where one is required, to nothing
  // otherwise). Their presence is what keeps the interface source compilable
  // and correctly linked on every platform.
#ifdef DPI_DLLISPEC
  SUCCEED();
#else
  FAIL() << "svdpi.h must define the platform import decoration macro";
#endif
#ifdef DPI_DLLESPEC
  SUCCEED();
#else
  FAIL() << "svdpi.h must define the platform export decoration macro";
#endif
}

}  // namespace
}  // namespace delta
