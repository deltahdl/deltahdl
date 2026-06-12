#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.63 Process: the object model diagram draws process (with its initial,
// final, and always members) traversing to and from module and stmt, and gives
// the process class one property access edge - "-> always type", int:
// vpiAlwaysType. The module<->process, process<->stmt, and stmt->scope edges are
// the generic one-to-one/one-to-many traversals already provided by the data
// model; the clause's only numbered Detail governs the property edge. Detail 1
// restricts vpiAlwaysType to exactly four constants. These tests observe the
// production code apply that restriction (the VpiIsAlwaysType guard) through the
// public vpi_get(vpiAlwaysType) dispatch path - both the legal values it admits
// and the values it rejects to vpiUndefined.

// The fixture installs a context so the public vpi_get entry point runs its real
// dispatch over the test objects.
class Process : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1 applied through the public dispatch: a process carrying one of the four
// always types reports exactly that constant through vpi_get(vpiAlwaysType).
// Driving all four legal constants here also exercises the admitting branch of
// the VpiIsAlwaysType guard, since a value the guard rejected would come back as
// vpiUndefined rather than the constant.
TEST_F(Process, ProcessReportsItsAlwaysTypeThroughVpiGet) {
  for (int always_type :
       {vpiAlways, vpiAlwaysComb, vpiAlwaysFF, vpiAlwaysLatch}) {
    VpiObject process;
    process.type = vpiAlways;
    process.always_type = always_type;
    EXPECT_EQ(vpi_get(vpiAlwaysType, &process), always_type)
        << "always_type constant " << always_type;
  }
}

// D1 applied through the public dispatch: a process with no legal always type
// reports vpiUndefined rather than handing back a value outside the four. This
// is the outcome that distinguishes the clause's restriction, applied by the
// production guard, from simply returning the stored field - covering both an
// unset always_type (an initial or final process) and a stored value that is not
// one of the four.
TEST_F(Process, ProcessWithoutALegalAlwaysTypeReportsUndefined) {
  VpiObject initial_process;
  initial_process.type = vpiInitial;  // not an always procedure; always_type 0
  EXPECT_EQ(vpi_get(vpiAlwaysType, &initial_process), vpiUndefined);

  VpiObject bad_process;
  bad_process.type = vpiAlways;
  bad_process.always_type = vpiInitial;  // a value outside the four
  EXPECT_EQ(vpi_get(vpiAlwaysType, &bad_process), vpiUndefined);
}

}  // namespace
}  // namespace delta
