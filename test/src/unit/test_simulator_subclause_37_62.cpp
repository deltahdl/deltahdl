#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.62 Event statement: the object model diagram draws the event statement
// object traversing to the named event it triggers, and gives the event
// statement one property access edge - "-> blocking", bool: vpiBlocking. The
// event-stmt->named-event edge is the generic one-to-one traversal already
// provided by the data model (and the named event object is owned by §37.27);
// the clause's only owned content is the Boolean property. These tests observe
// the production code apply that property through the public
// vpi_get(vpiBlocking) dispatch path - both the value it reports for an event
// statement and the vpiUndefined it returns for an object kind the property is
// not drawn on.

// The fixture installs a context so the public vpi_get entry point runs its
// real dispatch over the test objects.
class EventStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Applied through the public dispatch: an event statement reports its blocking
// flag through vpi_get(vpiBlocking), as 1 for a blocking trigger (->) and 0 for
// a nonblocking trigger (->>). Driving both states exercises the production
// code reading the stored Boolean rather than a constant.
TEST_F(EventStatement, EventStatementReportsBlockingFlagThroughVpiGet) {
  VpiObject blocking_trigger;
  blocking_trigger.type = vpiEventStmt;
  blocking_trigger.blocking = true;
  EXPECT_EQ(vpi_get(vpiBlocking, &blocking_trigger), 1);

  VpiObject nonblocking_trigger;
  nonblocking_trigger.type = vpiEventStmt;
  nonblocking_trigger.blocking = false;
  EXPECT_EQ(vpi_get(vpiBlocking, &nonblocking_trigger), 0);
}

// Applied through the public dispatch: vpiBlocking is drawn only on the event
// statement object, so querying it on any other object kind is not a valid
// request and the production guard returns vpiUndefined rather than handing
// back a stored field. This distinguishes the clause's property edge, applied
// by the guard, from an unconditional field read.
TEST_F(EventStatement, BlockingIsUndefinedForNonEventStatement) {
  VpiObject not_an_event_stmt;
  not_an_event_stmt.type = vpiAssignment;
  EXPECT_EQ(vpi_get(vpiBlocking, &not_an_event_stmt), vpiUndefined);
}

}  // namespace
}  // namespace delta
