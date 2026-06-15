#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.82 Active time format: the object model diagram carries a single edge,
// vpi_handle(vpiActiveTimeFormat, NULL) reaching the system task call - the
// $timeformat() call - that established the active time format. There is no BNF
// and no 'shall' BNF production, only one numbered detail:
//   1) if $timeformat() has not been called, vpi_handle(vpiActiveTimeFormat,
//      NULL) shall return NULL.
// The tf call object itself comes from §37.42 and vpi_handle from §38.6; this
// clause owns only the active-time-format relation and its not-yet-set rule.
// These tests drive the production dispatch through the public vpi_handle entry
// point after seeding the context's recorded $timeformat call.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch.
class ActiveTimeFormat : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Detail 1: with no $timeformat() call recorded - the state of a fresh context -
// vpi_handle(vpiActiveTimeFormat, NULL) returns NULL rather than reaching any
// object.
TEST_F(ActiveTimeFormat, ReturnsNullWhenTimeformatNotCalled) {
  EXPECT_EQ(VpiHandleC(vpiActiveTimeFormat, nullptr), nullptr);
}

// Diagram edge: once a $timeformat() call has set the active time format,
// vpi_handle(vpiActiveTimeFormat, NULL) reaches that system task call - and not
// some other null result, distinguishing it from the not-called case above.
TEST_F(ActiveTimeFormat, ReachesTheTimeformatCallThatSetTheFormat) {
  VpiObject timeformat_call;
  timeformat_call.type = vpiSysTaskCall;
  ctx_.SetActiveTimeFormatCall(&timeformat_call);

  EXPECT_EQ(VpiHandleC(vpiActiveTimeFormat, nullptr), &timeformat_call);
}

// Diagram edge / detail 1 both spell the traversal with a NULL second argument:
// the active-time-format relation originates only at the top-level reference. So
// even with a $timeformat() call on record, asking for vpiActiveTimeFormat
// relative to a concrete object must not reach that recorded call - the
// dispatch's null-reference guard keeps the relation scoped to the top level.
TEST_F(ActiveTimeFormat, DoesNotReachTheTimeformatCallFromANonNullReference) {
  VpiObject timeformat_call;
  timeformat_call.type = vpiSysTaskCall;
  ctx_.SetActiveTimeFormatCall(&timeformat_call);

  VpiObject some_object;
  some_object.type = vpiSysTaskCall;

  EXPECT_NE(VpiHandleC(vpiActiveTimeFormat, &some_object), &timeformat_call);
}

}  // namespace
}  // namespace delta
