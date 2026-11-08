#include <gtest/gtest.h>

#include <type_traits>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiPropertyAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiObject* ObjH() {
    net_.type = kVpiNet;
    net_.size = 8;
    net_.name = "bus";
    return &net_;
  }

  VpiObject net_;
  VpiContext ctx_;
};

TEST_F(VpiPropertyAccess, IntegerAndBooleanPropertiesComeFromVpiGet) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  PLI_INT32 vect_flag = vpi_get(vpiVector, obj_h);
  PLI_INT32 size = vpi_get(vpiSize, obj_h);

  EXPECT_EQ(vect_flag, 1);
  EXPECT_EQ(size, 8);
}

TEST_F(VpiPropertyAccess, AnIntegerPropertyIsOfTypePliInt32) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  static_assert(std::is_same_v<decltype(vpi_get(vpiSize, obj_h)), PLI_INT32>);
  EXPECT_EQ(sizeof(vpi_get(vpiSize, obj_h)), sizeof(PLI_INT32));
}

TEST_F(VpiPropertyAccess, AStringPropertyComesFromVpiGetStrAsPliByte8) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  PLI_BYTE8* name = vpi_get_str(vpiName, obj_h);

  static_assert(
      std::is_same_v<decltype(vpi_get_str(vpiName, obj_h)), PLI_BYTE8*>);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "bus");
}

TEST_F(VpiPropertyAccess, EachKindIsReadThroughItsOwnRoutine) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  EXPECT_EQ(vpi_get(vpiSize, obj_h), 8);
  EXPECT_EQ(vpi_get_str(vpiSize, obj_h), nullptr);
}

TEST_F(VpiPropertyAccess, AComplexValuePropertyComesFromItsOwnRoutine) {
  Arena arena;
  Variable backing;
  backing.value = MakeLogic4VecVal(arena, 32, 7u);

  VpiObject var;
  var.type = kVpiReg;
  var.var = &backing;

  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(VpiHandleOf(&var), &value);

  EXPECT_EQ(value.value.integer, 7);
}

}  // namespace
}  // namespace delta
