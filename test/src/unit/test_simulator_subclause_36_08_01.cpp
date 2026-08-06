#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.8.1: a sizetf application returns the number of bits the system
// function's return value is. These stubs return distinct widths so a test can
// observe that the value the sizetf returns - not a fixed constant - becomes
// the reported width.
int SizetfReturning12(const char*) { return 12; }
int SizetfReturning64(const char*) { return 64; }

// -----------------------------------------------------------------------------
// §36.8.1: "The value returned by the sizetf routine shall be the number of
// bits that the calltf routine shall provide as the return value for the system
// function." The width a sized system function reports is exactly whatever its
// sizetf application returns.
// -----------------------------------------------------------------------------

TEST(SizetfApplicationRoutine, ReturnValueIsTheFunctionReturnWidth) {
  VpiSystfData sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = &SizetfReturning12;

  // The width reported for the function is the value its sizetf returned.
  EXPECT_EQ(VpiSystfResultSizeBits(sized), 12);

  // A sizetf that returns a different value yields that different width, so the
  // reported size tracks the returned value rather than any fixed number.
  sized.sizetf = &SizetfReturning64;
  EXPECT_EQ(VpiSystfResultSizeBits(sized), 64);
}

// -----------------------------------------------------------------------------
// §36.8.1: "If no sizetf routine is specified, a user-defined system function
// shall return 32 bits."
// -----------------------------------------------------------------------------

TEST(SizetfApplicationRoutine, NoSizetfSpecifiedDefaultsTo32Bits) {
  VpiSystfData sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = nullptr;  // no sizetf application supplied

  EXPECT_EQ(VpiSystfResultSizeBits(sized), 32);
}

// -----------------------------------------------------------------------------
// §36.8.1: "The sizetf routine shall not be called for user-defined system
// tasks or for functions whose sysfunctype is set to vpiRealFunc." Whether a
// sizetf would run is decided before any call, so a system task and a
// real-valued function both report that the routine is not to be called - even
// when a sizetf application is supplied in the registration.
// -----------------------------------------------------------------------------

TEST(SizetfApplicationRoutine, NotCalledForSystemTask) {
  VpiSystfData task = {};
  task.type = kVpiSysTask;
  task.sizetf = &SizetfReturning12;  // present, but must not be consulted

  EXPECT_FALSE(VpiSystfSizetfIsCalled(task));
}

TEST(SizetfApplicationRoutine, NotCalledForRealValuedFunction) {
  VpiSystfData real_func = {};
  real_func.type = kVpiSysFunc;
  real_func.sysfunctype = kVpiRealFunc;
  real_func.sizetf = &SizetfReturning12;  // present, but must not be consulted

  EXPECT_FALSE(VpiSystfSizetfIsCalled(real_func));
}

}  // namespace
}  // namespace delta
