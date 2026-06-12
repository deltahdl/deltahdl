#include <gtest/gtest.h>

#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.6 (Object protection properties) states that every object carries a
// vpiIsProtected Boolean property - not drawn in the data model diagrams - that
// vpi_get() reports as TRUE when the handle denotes code sealed in a decryption
// envelope and FALSE otherwise. Unless otherwise specified, accessing any
// relationship or property of a protected object is an error; the vpiType and
// vpiIsProtected properties are the stated exception and shall be permitted for
// all objects. These tests drive the production routines through the public C
// entry points, exactly as a PLI program would, by installing a private context
// as the global one.
class VpiObjectProtection : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// Claim: every object has a vpiIsProtected property and vpi_get() reports it as
// a Boolean - FALSE for an ordinary object that holds no protected code.
TEST_F(VpiObjectProtection, GetIsProtectedReportsFalseForOrdinaryObject) {
  VpiObject net;
  net.type = vpiNet;
  // default-constructed objects are not protected
  EXPECT_EQ(vpi_get(vpiIsProtected, &net), 0);
}

// Claim: access to the vpiType property of a protected object shall be permitted
// for all objects - vpi_get(vpiType, ...) returns the real type constant rather
// than erroring, and leaves no error recorded.
TEST_F(VpiObjectProtection, GetTypeIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get(vpiType, &mod), vpiModule);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
}

// Claim: access to the vpiIsProtected property of a protected object is likewise
// permitted - it is not blocked by the protected-object guard and reports TRUE
// without recording an error.
TEST_F(VpiObjectProtection, GetIsProtectedIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get(vpiIsProtected, &mod), 1);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
}

// Claim: unless otherwise specified, access to a property of a protected object
// is an error. Any property other than the two permitted exceptions records an
// error and yields vpiUndefined, the value vpi_get() returns on an error.
TEST_F(VpiObjectProtection, GetOtherPropertyOnProtectedObjectIsAnError) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.size = 32;
  reg.is_protected = true;

  EXPECT_EQ(vpi_get(vpiSize, &reg), vpiUndefined);

  SVpiErrorInfo info = {};
  EXPECT_NE(VpiChkErrorC(&info), 0);
  EXPECT_NE(info.level, 0);
}

// Claim (string form of the permitted exception): vpiType remains accessible on
// a protected object through vpi_get_str, which hands back the type-constant
// name without recording an error.
TEST_F(VpiObjectProtection, GetStrTypeIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  const char* type_name = vpi_get_str(vpiType, &mod);
  ASSERT_NE(type_name, nullptr);
  EXPECT_EQ(std::string(type_name), "vpiModule");

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
}

// Claim (string form of the general rule): a string query for any other property
// of a protected object is an error - it records the error and supplies no
// string (a null pointer).
TEST_F(VpiObjectProtection, GetStrOtherPropertyOnProtectedObjectIsAnError) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "locked";
  mod.is_protected = true;

  EXPECT_EQ(vpi_get_str(vpiName, &mod), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_NE(VpiChkErrorC(&info), 0);
  EXPECT_NE(info.level, 0);
}

// Claim (string form of the second permitted exception): vpiIsProtected is, like
// vpiType, permitted on a protected object for all objects. Through vpi_get_str
// it has no string representation (it is a Boolean), so the call hands back a
// null pointer - but the protected-object guard must not have fired, so no error
// is recorded. This distinguishes the permitted exception (silent null) from a
// blocked property (null plus a recorded error).
TEST_F(VpiObjectProtection, GetStrIsProtectedIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get_str(vpiIsProtected, &mod), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
}

// Edge (boundary of the protected-object rule): the access error applies only to
// protected objects. An ordinary object reports a non-exception property such as
// vpiSize normally and records no error, confirming the guard keys off the
// object's protection state rather than the property being requested.
TEST_F(VpiObjectProtection, GetNonExceptionPropertyOnOrdinaryObjectSucceeds) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.size = 16;
  // not protected

  EXPECT_EQ(vpi_get(vpiSize, &reg), 16);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
}

}  // namespace
}  // namespace delta
