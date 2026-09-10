#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"
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

// How many times the counting sizetf below has run. §36.8.1 bounds that at one
// per registration, so the count is the whole subject of the case that reads
// it.
int g_sizetf_runs = 0;

int CountingSizetfReturning17(const char*) {
  ++g_sizetf_runs;
  return 17;
}

int PutsFortyTwoCalltf(const char*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 42;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

class SizetfInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.8.1: "Each sizetf routine shall be called at most once." The width is
// asked for three times and the routine runs once, every later ask answering
// with what that run returned. Asked straight through VpiSystfResultSizeBits,
// which measures a record rather than a registration, the same three asks run
// it three times -- that free function is what the cases above use, and it is
// the registration that carries the once.
TEST_F(SizetfInARun, ASizetfRunsOncePerRegistration) {
  g_sizetf_runs = 0;
  s_vpi_systf_data sized = {};
  sized.type = vpiSysFunc;
  sized.sysfunctype = vpiSizedFunc;
  sized.tfname = "$sized_once";
  sized.sizetf = &CountingSizetfReturning17;
  ASSERT_NE(vpi_register_systf(&sized), nullptr);

  const VpiSystfData* registered = vpi_ctx_.ResolveSystf("$sized_once");
  ASSERT_NE(registered, nullptr);

  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(g_sizetf_runs, 1);
}

// §36.8.1: "It shall be called if its associated system function appears in the
// design." The design calls $sized_once once, and that is what runs the sizetf
// -- registering it did not.
TEST_F(SizetfInARun, ASizetfRunsBecauseTheFunctionAppearsInTheDesign) {
  g_sizetf_runs = 0;
  s_vpi_systf_data sized = {};
  sized.type = vpiSysFunc;
  sized.sysfunctype = vpiSizedFunc;
  sized.tfname = "$sized_once";
  sized.sizetf = &CountingSizetfReturning17;
  sized.calltf = &PutsFortyTwoCalltf;
  ASSERT_NE(vpi_register_systf(&sized), nullptr);
  EXPECT_EQ(g_sizetf_runs, 0);

  SimFixture f;
  RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  initial r = $sized_once();\n"
      "endmodule\n",
      f, "r");

  EXPECT_EQ(g_sizetf_runs, 1);
}

// §36.8.1: "The value returned by the sizetf routine shall be the number of
// bits that the calltf routine shall provide as the return value for the system
// function." The sizetf answers 17, so the value the application writes through
// is seventeen bits wide -- not the thirty-two §38.37.1 gives a sized function
// that supplies no sizetf, which is what the call answered with before.
TEST_F(SizetfInARun, TheCallsResultIsAsWideAsTheSizetfSaid) {
  g_sizetf_runs = 0;
  s_vpi_systf_data sized = {};
  sized.type = vpiSysFunc;
  sized.sysfunctype = vpiSizedFunc;
  sized.tfname = "$sized_once";
  sized.sizetf = &CountingSizetfReturning17;
  sized.calltf = &PutsFortyTwoCalltf;
  ASSERT_NE(vpi_register_systf(&sized), nullptr);

  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  initial r = $sized_once();\n"
      "endmodule\n",
      f, "r");

  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  const VpiSystfData* registered = vpi_ctx_.ResolveSystf("$sized_once");
  ASSERT_NE(registered, nullptr);
  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(g_sizetf_runs, 1);
}

}  // namespace
}  // namespace delta
