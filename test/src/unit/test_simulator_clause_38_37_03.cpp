#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.37.3 describes registering multiple system tasks and system functions.
// It is purely descriptive: it names two ways to do so and gives an example,
// without any BNF or normative "shall" of its own. The first way - separate
// s_vpi_systf_data structures with one vpi_register_systf() call each - is the
// method already exercised by §38.37.1 and §38.37.2, so it needs nothing new
// here. The distinctive way is the second: a single static array of
// s_vpi_systf_data records whose final element has a type of 0, so the
// registration calls can be driven by a loop that stops when it reaches that
// 0. The registration entry point itself comes from §38.37.1; these tests
// observe that existing machinery realizing §38.37.3's array-and-loop method.

class RegisterMultipleSystfs : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// Stub callback applications referenced by the array entries below. §38.37.3
// only concerns how the records are registered, not what the callbacks do, so
// these are inert.
int MyTaskCalltf(const char*) { return 0; }
int MyIntFuncCalltf(const char*) { return 0; }
int MyIntFuncComptf(const char*) { return 0; }
int MySizedFuncCalltf(const char*) { return 0; }
int MySizedFuncComptf(const char*) { return 0; }
int MySizedFuncSizetf(const char*) { return 32; }

// §38.37.3 (second method): a static array of s_vpi_systf_data structures, with
// a final element whose type is 0, registered by a loop that calls
// vpi_register_systf() once per structure and terminates when it reaches the 0.
// This mirrors the standard's example, which declares one system task and two
// system functions (an integer function and a sized function) in a single
// array. Walking it leaves every non-sentinel structure registered.
TEST_F(RegisterMultipleSystfs, StaticArrayLoopRegistersEachStructure) {
  static s_vpi_systf_data systf_test_list[] = {
      {vpiSysTask, 0, "$my_task", &MyTaskCalltf, nullptr, nullptr, nullptr},
      {vpiSysFunc, vpiIntFunc, "$my_int_func", &MyIntFuncCalltf, &MyIntFuncComptf,
       nullptr, nullptr},
      {vpiSysFunc, vpiSizedFunc, "$my_sized_func", &MySizedFuncCalltf,
       &MySizedFuncComptf, &MySizedFuncSizetf, nullptr},
      {0, 0, nullptr, nullptr, nullptr, nullptr, nullptr},
  };

  // The 0-typed final element lets the calls be placed in a loop that ends when
  // it reaches that 0, exactly as shown in §38.37.3.
  for (s_vpi_systf_data* p = &systf_test_list[0]; p->type != 0; ++p) {
    vpi_register_systf(p);
  }

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 3u);

  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$my_task");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysTask);

  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[1].tfname, "$my_int_func");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].sysfunctype, vpiIntFunc);

  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[2].tfname, "$my_sized_func");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[2].type, vpiSysFunc);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[2].sysfunctype, vpiSizedFunc);
}

// §38.37.3: it is the 0-typed final element that terminates the loop - not the
// physical end of the array. An entry placed after the 0 sentinel is never
// reached, so it is left unregistered. This isolates the terminator's role from
// mere array exhaustion.
TEST_F(RegisterMultipleSystfs, ZeroTypeSentinelTerminatesTheLoop) {
  static s_vpi_systf_data systf_test_list[] = {
      {vpiSysTask, 0, "$before_sentinel", &MyTaskCalltf, nullptr, nullptr,
       nullptr},
      {0, 0, nullptr, nullptr, nullptr, nullptr, nullptr},
      // A well-formed structure beyond the sentinel: a correct loop never sees
      // it.
      {vpiSysTask, 0, "$after_sentinel", &MyTaskCalltf, nullptr, nullptr,
       nullptr},
  };

  for (s_vpi_systf_data* p = &systf_test_list[0]; p->type != 0; ++p) {
    vpi_register_systf(p);
  }

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1u);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$before_sentinel");
}

}  // namespace
}  // namespace delta
