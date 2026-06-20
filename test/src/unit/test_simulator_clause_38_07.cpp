#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.7: vpi_get64() reads the value of a 64-bit integer object property (one
// whose type is PLI_INT64). Querying a protected object is an error, and on any
// error the routine returns vpiUndefined.
class VpiGet64Sim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §38.7: a 64-bit integer property is returned at full PLI_INT64 width. A class
// object's identifier (§37.33) is genuinely 64-bit; an identifier larger than
// what fits in PLI_INT32 comes back intact, whereas vpi_get() must narrow the
// same value and so reports something different.
TEST_F(VpiGet64Sim, ReturnsSixtyFourBitPropertyAtFullWidth) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.obj_id = static_cast<int64_t>(0x1'0000'0002);  // > INT32_MAX

  EXPECT_EQ(vpi_get64(vpiObjId, &class_obj),
            static_cast<PLI_INT64>(0x1'0000'0002));
  // The 32-bit reader cannot carry the full value, so the 64-bit path is what
  // preserves it.
  EXPECT_NE(static_cast<PLI_INT64>(vpi_get(vpiObjId, &class_obj)),
            vpi_get64(vpiObjId, &class_obj));
}

// §38.7: querying a protected object is an error, and on an error vpi_get64()
// returns vpiUndefined.
TEST_F(VpiGet64Sim, ProtectedObjectQueryReturnsVpiUndefined) {
  VpiObject locked;
  locked.type = vpiClassObj;
  locked.obj_id = 5;
  locked.is_protected = true;

  EXPECT_EQ(vpi_get64(vpiObjId, &locked), vpiUndefined);

  // The refused query is recorded as an error.
  SVpiErrorInfo info = {};
  EXPECT_NE(VpiChkErrorC(&info), 0);
  EXPECT_NE(info.level, 0);
}

// §38.7: a null object handle has no property to read; the routine returns 0.
TEST_F(VpiGet64Sim, NullHandleReturnsZero) {
  EXPECT_EQ(vpi_get64(vpiObjId, nullptr), 0);
}

}  // namespace
}  // namespace delta
