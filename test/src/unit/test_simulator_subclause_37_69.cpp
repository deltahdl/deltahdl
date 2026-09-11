#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.69 Repeat control: the object model diagram draws a repeat control with
// two unlabeled edges - one to a count expression (the vpiExpr relation) and
// one to an event control (the vpiEventControl relation). It carries no
// numbered Details and no 'shall' sentences. These tests observe the production
// code that serves the diagram's relations: the count edge through the
// dedicated helper VpiRepeatControlExpr (wired into vpi_handle), and the
// event-control edge through the generic traversal, since an event control's
// own type is vpiEventControl.
//
// The count edge is drawn to `expr`, which §37.59 makes a class holding the
// `simple expr` class among its members, and §37.58 draws that one holding a
// parameter, a spec param, a var select and a bit select beside the ref obj.
// Only the ref obj was admitted as a simple expression, so a repeat count
// written "repeat (p)" over a parameter or "repeat (n[0])" over a bit of a
// vector reached nothing through the edge the figure draws it on.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class RepeatControl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Count edge: a repeat control reaches its count expression through the public
// vpi_handle(vpiExpr, ...) dispatch path.
TEST_F(RepeatControl, RepeatControlReachesCountThroughVpiExpr) {
  VpiObject count;
  count.type = vpiOperation;  // an expression kind

  VpiObject event_control;
  event_control.type = vpiEventControl;

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&count, &event_control};

  EXPECT_EQ(vpi_handle(vpiExpr, &repeat_control), &count);
}

// Count edge: the count is found even when the event control child precedes it
// in the child list. The scan skips the non-expression event control and
// returns the first expression child.
TEST_F(RepeatControl, CountFoundWhenItFollowsTheEventControlChild) {
  VpiObject event_control;
  event_control.type = vpiEventControl;  // a non-expression child, listed first

  VpiObject count;
  count.type = vpiRefObj;  // another expression kind

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&event_control, &count};

  EXPECT_EQ(vpi_handle(vpiExpr, &repeat_control), &count);
}

// Count edge: a null handle and a repeat control with no expression child both
// report no count.
TEST_F(RepeatControl, CountIsNullWhenAbsentOrHandleNull) {
  EXPECT_EQ(VpiRepeatControlExpr(nullptr), nullptr);

  VpiObject event_control;
  event_control.type = vpiEventControl;

  VpiObject bare_repeat;
  bare_repeat.type = vpiRepeatControl;
  bare_repeat.children = {&event_control};  // only an event control, no count
  EXPECT_EQ(VpiRepeatControlExpr(&bare_repeat), nullptr);
}

// Count edge is scoped to the repeat control: asking another object that owns
// an expression child for vpiExpr through this path does not pick up that
// child. A while statement reaches an expression only through vpiCondition
// (§37.66), so it reports nothing through the vpiExpr count edge owned here.
TEST_F(RepeatControl, VpiExprCountIsScopedToRepeatControl) {
  VpiObject expr_child;
  expr_child.type = vpiOperation;

  VpiObject loop;
  loop.type = vpiWhile;  // not a repeat control; draws its own relations
  loop.children = {&expr_child};

  EXPECT_EQ(vpi_handle(vpiExpr, &loop), nullptr);
}

// Event-control edge (the diagram's other unlabeled arrow): a repeat control
// reaches its event control through the generic vpiEventControl traversal,
// since an event control's own type is vpiEventControl.
TEST_F(RepeatControl, EventControlReachedThroughGenericTraversal) {
  VpiObject count;
  count.type = vpiOperation;

  VpiObject event_control;
  event_control.type = vpiEventControl;

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&count, &event_control};

  EXPECT_EQ(vpi_handle(vpiEventControl, &repeat_control), &event_control);
}

// Count edge: the count is a member of the expr class however the source wrote
// it. A parameter, a spec param, a var select and a bit select are the members
// §37.58's `simple expr` class holds beside the reference, so each stands as a
// repeat count and is reached through the same edge.
TEST_F(RepeatControl, CountReachesEverySimpleExpressionKind) {
  for (int count_kind :
       {vpiParameter, vpiSpecParam, vpiVarSelect, vpiBitSelect}) {
    VpiObject count;
    count.type = count_kind;

    VpiObject event_control;
    event_control.type = vpiEventControl;

    VpiObject repeat_control;
    repeat_control.type = vpiRepeatControl;
    // The event control precedes the count, so a scan that returned the first
    // child rather than the first expression would answer with it instead.
    repeat_control.children = {&event_control, &count};

    EXPECT_EQ(vpi_handle(vpiExpr, &repeat_control), &count)
        << "count kind " << count_kind;
  }
}

// Event-control edge: a repeat control written with a count and no event
// control reaches none, so the count is not handed back for both of the two
// arrows the figure draws from one object.
TEST_F(RepeatControl, EventControlIsNullWhenTheRepeatControlCarriesNone) {
  VpiObject count;
  count.type = vpiOperation;

  VpiObject repeat_control;
  repeat_control.type = vpiRepeatControl;
  repeat_control.children = {&count};

  EXPECT_EQ(vpi_handle(vpiEventControl, &repeat_control), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, &repeat_control), &count);
}

}  // namespace
}  // namespace delta
