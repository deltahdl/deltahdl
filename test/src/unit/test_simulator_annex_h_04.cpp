#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <type_traits>

#include "simulator/svdpi.h"

namespace delta {
namespace {

TEST(SvdpiPortability, ScalarTypesHaveFixedSingleByteRepresentation) {
  EXPECT_EQ(sizeof(svScalar), 1u);
  EXPECT_EQ(sizeof(svBit), 1u);
  EXPECT_EQ(sizeof(svLogic), 1u);

  EXPECT_TRUE(std::is_unsigned<svScalar>::value);
  EXPECT_TRUE(std::is_unsigned<svBit>::value);
  EXPECT_TRUE(std::is_unsigned<svLogic>::value);

  EXPECT_EQ(std::numeric_limits<svScalar>::digits, 8);

  EXPECT_EQ(static_cast<svScalar>(sv_0), 0);
  EXPECT_EQ(static_cast<svScalar>(sv_1), 1);
  EXPECT_EQ(static_cast<svScalar>(sv_z), 2);
  EXPECT_EQ(static_cast<svScalar>(sv_x), 3);
}

TEST(SvdpiPortability, BitVectorWordIsFixedThirtyTwoBits) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_TRUE(std::is_unsigned<svBitVecVal>::value);
  EXPECT_EQ(std::numeric_limits<svBitVecVal>::digits, 32);

  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
}

TEST(SvdpiPortability, LogicVectorWordHasFixedTwoWordLayout) {
  EXPECT_EQ(sizeof(s_vpi_vecval), 8u);
  EXPECT_EQ(offsetof(s_vpi_vecval, aval), 0u);
  EXPECT_EQ(offsetof(s_vpi_vecval, bval), 4u);
  EXPECT_EQ(sizeof(reinterpret_cast<s_vpi_vecval*>(0)->aval), 4u);
  EXPECT_EQ(sizeof(reinterpret_cast<s_vpi_vecval*>(0)->bval), 4u);

  EXPECT_TRUE((std::is_same<svLogicVecVal, s_vpi_vecval>::value));
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

TEST(SvdpiPortability, HandlesAreOpaquePointerSized) {
  EXPECT_EQ(sizeof(svScope), sizeof(void*));
  EXPECT_EQ(sizeof(svOpenArrayHandle), sizeof(void*));

  EXPECT_TRUE(std::is_pointer<svScope>::value);
  EXPECT_TRUE(std::is_pointer<svOpenArrayHandle>::value);

  svScope scope = nullptr;
  svOpenArrayHandle array = nullptr;
  EXPECT_EQ(scope, nullptr);
  EXPECT_EQ(array, nullptr);
}

TEST(SvdpiPortability, PlatformLinkageDecorationIsProvided) {
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

extern "C" const char* svDpiVersion(void);
extern "C" svBit svGetBitselBit(const svBitVecVal* s, int i);
extern "C" int svLeft(svOpenArrayHandle h, int d);
extern "C" int svSize(svOpenArrayHandle h, int d);
extern "C" void* svGetArrElemPtr(svOpenArrayHandle h, int indx1, ...);
extern "C" svScope svGetScope(void);
extern "C" svScope svSetScope(svScope scope);
extern "C" const char* svGetNameFromScope(svScope scope);
extern "C" int svIsDisabledState(void);
extern "C" int svGetTime(svScope scope, svTimeVal* time);

namespace delta {
namespace {

TEST(SvdpiPortability, InterfaceFunctionsHaveCLinkage) {
  EXPECT_NE(svDpiVersion(), nullptr);
  svScope current = svGetScope();
  EXPECT_EQ(svSetScope(current), current);
}

}  // namespace
}  // namespace delta
