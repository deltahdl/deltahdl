#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.3.2 governs overriding built-in system task and system function names.
// Built-in system tasks/functions (Clause 20, Clause 21, and tool-specific
// ones) live in the same '$'-prefixed namespace as user-defined names. When a
// user-provided PLI application is registered (through the PLI mechanism of
// §36.9.1) under a built-in name, that application overrides the built-in. The
// production carrier is the simulator's system-task/function registry, whose
// ResolveSystf() consults the registry first and returns the overriding
// application for a name, falling back (null) to the built-in when none claims
// it.
class OverrideBuiltinSystf : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.3.2: with no PLI application registered under a built-in name, nothing
// overrides it - resolving the name finds no registration, so the built-in
// stands.
TEST_F(OverrideBuiltinSystf, UnclaimedBuiltinNameResolvesToNothing) {
  EXPECT_EQ(vpi_ctx_.ResolveSystf("$random"), nullptr);
}

// §36.3.2: if a user-provided PLI application is associated with the same name
// as a built-in system function, the user application shall override the
// built-in. After registering an application under the built-in name, resolving
// that name returns the user application (here, its calltf), not the built-in.
TEST_F(OverrideBuiltinSystf, UserApplicationOverridesBuiltinName) {
  static int kCalled = 0;
  kCalled = 0;
  auto user_random = [](const char*) -> int {
    kCalled = 1;
    return 0;
  };

  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.tfname = "$random";
  data.calltf = user_random;

  ASSERT_NE(vpi_register_systf(&data), nullptr);

  const VpiSystfData* resolved = vpi_ctx_.ResolveSystf("$random");
  ASSERT_NE(resolved, nullptr);
  EXPECT_STREQ(resolved->tfname, "$random");
  ASSERT_NE(resolved->calltf, nullptr);

  // The resolved application is the user's: invoking its calltf runs the
  // user-provided functionality that replaced the built-in $random.
  resolved->calltf(nullptr);
  EXPECT_EQ(kCalled, 1);
}

// §36.3.2: the override replaces the built-in's functionality. Modelling a
// built-in registered ahead of a user application sharing the name, resolving
// the name returns the most recently registered (user) application, so the user
// version is the one that runs.
TEST_F(OverrideBuiltinSystf, LaterRegistrationOverridesEarlierOfSameName) {
  auto builtin_impl = [](const char*) -> int { return 1; };
  auto user_impl = [](const char*) -> int { return 2; };

  s_vpi_systf_data builtin = {};
  builtin.type = vpiSysFunc;
  builtin.tfname = "$random";
  builtin.calltf = builtin_impl;

  s_vpi_systf_data user = {};
  user.type = vpiSysFunc;
  user.tfname = "$random";
  user.calltf = user_impl;

  ASSERT_NE(vpi_register_systf(&builtin), nullptr);
  ASSERT_NE(vpi_register_systf(&user), nullptr);

  const VpiSystfData* resolved = vpi_ctx_.ResolveSystf("$random");
  ASSERT_NE(resolved, nullptr);
  ASSERT_NE(resolved->calltf, nullptr);
  // The overriding (later, user) application is resolved, not the earlier one.
  EXPECT_EQ(resolved->calltf(nullptr), 2);
}

// §36.3.2: the built-in system functions $signed and $unsigned can be
// overridden. Registering user applications under those names is accepted and
// each resolves to its own override.
TEST_F(OverrideBuiltinSystf, SignedAndUnsignedCanBeOverridden) {
  s_vpi_systf_data signed_fn = {};
  signed_fn.type = vpiSysFunc;
  signed_fn.sysfunctype = vpiSizedSignedFunc;
  signed_fn.tfname = "$signed";

  s_vpi_systf_data unsigned_fn = {};
  unsigned_fn.type = vpiSysFunc;
  unsigned_fn.sysfunctype = vpiSizedFunc;
  unsigned_fn.tfname = "$unsigned";

  ASSERT_NE(vpi_register_systf(&signed_fn), nullptr);
  ASSERT_NE(vpi_register_systf(&unsigned_fn), nullptr);

  const VpiSystfData* rs = vpi_ctx_.ResolveSystf("$signed");
  const VpiSystfData* ru = vpi_ctx_.ResolveSystf("$unsigned");
  ASSERT_NE(rs, nullptr);
  ASSERT_NE(ru, nullptr);
  EXPECT_STREQ(rs->tfname, "$signed");
  EXPECT_STREQ(ru->tfname, "$unsigned");
}

// §36.3.2: $signed and $unsigned are unique in that the return width is based on
// the width of their argument. When overridden, the PLI version shall have the
// same return width for all instances of the system function, and that width is
// defined by the PLI sizetf routine. Resolving the overridden name and reading
// its sizetf-defined result width yields the same width on every query (every
// instance), rather than varying per call.
TEST_F(OverrideBuiltinSystf, OverriddenSignedHasSameWidthForAllInstances) {
  auto fixed_width = [](const char*) -> int { return 17; };

  s_vpi_systf_data signed_fn = {};
  signed_fn.type = vpiSysFunc;
  signed_fn.sysfunctype = vpiSizedSignedFunc;
  signed_fn.tfname = "$signed";
  signed_fn.sizetf = fixed_width;

  ASSERT_NE(vpi_register_systf(&signed_fn), nullptr);

  const VpiSystfData* resolved = vpi_ctx_.ResolveSystf("$signed");
  ASSERT_NE(resolved, nullptr);

  // The sizetf routine defines the PLI return width; it is the same for every
  // instance of the overridden system function.
  int first = VpiSystfResultSizeBits(*resolved);
  int second = VpiSystfResultSizeBits(*resolved);
  EXPECT_EQ(first, 17);
  EXPECT_EQ(second, 17);
  EXPECT_EQ(first, second);
}

// §36.3.2 edge: the override rule keys on a system task/function name. Asking to
// resolve a null name names nothing, so no override is found and the lookup
// reports none (the built-in, if any, would stand) rather than dereferencing.
TEST_F(OverrideBuiltinSystf, NullNameResolvesToNothing) {
  EXPECT_EQ(vpi_ctx_.ResolveSystf(nullptr), nullptr);
}

// §36.3.2: the override applies to a built-in system task as well as a system
// function - the rule speaks of "system task or system function". A user
// application registered as a task under a built-in name is the override that
// resolves for that name.
TEST_F(OverrideBuiltinSystf, UserTaskApplicationOverridesBuiltinName) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$monitor";

  ASSERT_NE(vpi_register_systf(&task), nullptr);

  const VpiSystfData* resolved = vpi_ctx_.ResolveSystf("$monitor");
  ASSERT_NE(resolved, nullptr);
  EXPECT_STREQ(resolved->tfname, "$monitor");
  EXPECT_EQ(resolved->type, vpiSysTask);
}

// §36.3.2 edge: only a registration sharing the name overrides a built-in.
// With other applications registered but none under the queried built-in name,
// nothing claims it, so the lookup finds no override and the built-in stands.
TEST_F(OverrideBuiltinSystf, NonMatchingRegistrationsLeaveBuiltinNameUnclaimed) {
  s_vpi_systf_data other = {};
  other.type = vpiSysFunc;
  other.tfname = "$my_func";

  ASSERT_NE(vpi_register_systf(&other), nullptr);

  EXPECT_EQ(vpi_ctx_.ResolveSystf("$random"), nullptr);
}

}  // namespace
}  // namespace delta
