#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class RepeatControl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(RepeatControl, RepeatControlReachesCountThroughVpiExpr) {
  VpiObject count;
  count.type = vpiOperation;

  VpiObject event_control;
  event_control.type = vpiEventControl;

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&count, &event_control};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&repeat_control))),
            &count);
}

TEST_F(RepeatControl, CountFoundWhenItFollowsTheEventControlChild) {
  VpiObject event_control;
  event_control.type = vpiEventControl;

  VpiObject count;
  count.type = vpiRefObj;

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&event_control, &count};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&repeat_control))),
            &count);
}

TEST_F(RepeatControl, CountIsNullWhenAbsentOrHandleNull) {
  EXPECT_EQ(VpiRepeatControlExpr(nullptr), nullptr);

  VpiObject event_control;
  event_control.type = vpiEventControl;

  VpiObject bare_repeat;
  bare_repeat.type = vpiRepeatControl;
  bare_repeat.children = {&event_control};
  EXPECT_EQ(VpiRepeatControlExpr(&bare_repeat), nullptr);
}

TEST_F(RepeatControl, VpiExprCountIsScopedToRepeatControl) {
  VpiObject expr_child;
  expr_child.type = vpiOperation;

  VpiObject loop;
  loop.type = vpiWhile;
  loop.children = {&expr_child};

  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&loop)), nullptr);
}

TEST_F(RepeatControl, EventControlReachedThroughGenericTraversal) {
  VpiObject count;
  count.type = vpiOperation;

  VpiObject event_control;
  event_control.type = vpiEventControl;

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&count, &event_control};

  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiEventControl, VpiHandleOf(&repeat_control))),
      &event_control);
}

TEST_F(RepeatControl, CountReachesEverySimpleExpressionKind) {
  for (int count_kind :
       {vpiParameter, vpiSpecParam, vpiVarSelect, vpiBitSelect}) {
    VpiObject count;
    count.type = count_kind;

    VpiObject event_control;
    event_control.type = vpiEventControl;

    VpiObject repeat_control;
    repeat_control.type = vpiRepeatControl;
    repeat_control.children = {&event_control, &count};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&repeat_control))),
              &count)
        << "count kind " << count_kind;
  }
}

TEST_F(RepeatControl, EventControlIsNullWhenTheRepeatControlCarriesNone) {
  VpiObject count;
  count.type = vpiOperation;

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&count};

  EXPECT_EQ(vpi_handle(vpiEventControl, VpiHandleOf(&repeat_control)), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&repeat_control))),
            &count);
}

}  // namespace
}  // namespace delta
