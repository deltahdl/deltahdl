#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiGet64Sim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiGet64Sim, ReturnsSixtyFourBitPropertyAtFullWidth) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.obj_id = static_cast<int64_t>(0x1'0000'0002);

  EXPECT_EQ(vpi_get64(vpiObjId, VpiHandleOf(&class_obj)),
            static_cast<PLI_INT64>(0x1'0000'0002));
  EXPECT_NE(static_cast<PLI_INT64>(vpi_get(vpiObjId, VpiHandleOf(&class_obj))),
            vpi_get64(vpiObjId, VpiHandleOf(&class_obj)));
}

TEST_F(VpiGet64Sim, ProtectedObjectQueryReturnsVpiUndefined) {
  VpiObject locked;
  locked.type = vpiClassObj;
  locked.obj_id = 5;
  locked.is_protected = true;

  EXPECT_EQ(vpi_get64(vpiObjId, VpiHandleOf(&locked)), vpiUndefined);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

TEST_F(VpiGet64Sim, TheProtectedRuleKeepsTheExceptionsSpecifiedElsewhere) {
  VpiObject locked;
  locked.type = vpiClassObj;
  locked.is_protected = true;

  EXPECT_EQ(vpi_get64(vpiType, VpiHandleOf(&locked)), vpiClassObj);
  EXPECT_EQ(vpi_get64(vpiIsProtected, VpiHandleOf(&locked)), 1);

  VpiObject locked_expr;
  locked_expr.type = vpiOperation;
  locked_expr.is_protected = true;
  locked_expr.size = 16;

  EXPECT_EQ(vpi_get64(vpiSize, VpiHandleOf(&locked_expr)), 16);
}

TEST_F(VpiGet64Sim, ANullHandleReadsTheSameRunWideAnswersVpiGetReads) {
  VpiHandle module = vpi_ctx_.CreateModule("t", "t");
  module->time_precision = -9;

  ASSERT_EQ(vpi_get(vpiTimePrecision, nullptr), -9);
  EXPECT_EQ(vpi_get64(vpiTimePrecision, nullptr), -9);
  EXPECT_EQ(vpi_get64(vpiTimeUnit, nullptr), vpi_get(vpiTimeUnit, nullptr));

  ASSERT_NE(vpi_get(vpiSaveRestartID, nullptr), 0);
  EXPECT_EQ(vpi_get64(vpiSaveRestartID, nullptr),
            vpi_get(vpiSaveRestartID, nullptr));

  EXPECT_EQ(vpi_get64(vpiObjId, nullptr), vpiUndefined);
}

TEST_F(VpiGet64Sim, AProtectedNonExpressionRefusesItsSize) {
  VpiObject locked;
  locked.type = vpiClassObj;
  locked.is_protected = true;
  locked.size = 16;
  EXPECT_EQ(vpi_get64(vpiSize, VpiHandleOf(&locked)), vpiUndefined);
}

}  // namespace
}  // namespace delta
