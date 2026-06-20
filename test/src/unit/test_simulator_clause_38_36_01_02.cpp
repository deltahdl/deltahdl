#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36.1.2 ("Behavior by statement type") states that every possible object
// within the statement class qualifies for having a cbStmt callback placed on
// it, and Table 38-6 enumerates exactly those objects: the blocks (begin, named
// begin, fork, named fork), the conditionals (if, if-else), the loops (while,
// repeat, for, forever), the procedural statements that fire just before they
// execute (wait, case, assignment, procedural-assign/deassign, disable, force,
// release, event), the timing controls (delay control, event control), and the
// task calls (task call, system-task call). The per-type rows of Table 38-6
// describe only the run-time instant at which the callback fires; the
// registration path that accepts these objects as cbStmt targets is the one
// established by §38.36.1.1, so the qualifying-object rule is already in force.
// These tests observe vpi_register_cb() accepting a cbStmt callback on every
// one of the enumerated statement-class objects.

// The full Table 38-6 object set. Each is a member of the statement class and
// so qualifies as a cbStmt target.
struct StmtObject {
  int type;
  const char* label;
};

constexpr StmtObject kTable386Objects[] = {
    {vpiBegin, "begin"},
    {vpiNamedBegin, "named begin"},
    {vpiFork, "fork"},
    {vpiNamedFork, "named fork"},
    {vpiIf, "if"},
    {vpiIfElse, "if-else"},
    {vpiWhile, "while"},
    {vpiRepeat, "repeat"},
    {vpiFor, "for"},
    {vpiForever, "forever"},
    {vpiWait, "wait"},
    {vpiCase, "case"},
    {vpiAssignment, "assignment"},
    {vpiAssignStmt, "assign statement"},
    {vpiDeassign, "deassign"},
    {vpiDisable, "disable"},
    {vpiForce, "force"},
    {vpiRelease, "release"},
    {vpiEventStmt, "event statement"},
    {vpiDelayControl, "delay control"},
    {vpiEventControl, "event control"},
    {vpiTaskCall, "task call"},
    {vpiSysTaskCall, "system-task call"},
};

class VpiStmtCallbackByType : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a handle that stands for a statement object of the given VPI type.
  // The handle is created from a named variable and then retyped, so any object
  // kind in Table 38-6 can be presented to vpi_register_cb().
  vpiHandle MakeHandleOfType(const char* name, int type) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(name, nullptr);
    if (h) h->type = type;
    return h;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.36.1.2: every object within the statement class qualifies for a cbStmt
// callback. Registering a cbStmt callback on each of the objects enumerated in
// Table 38-6 succeeds and yields a callback handle.
TEST_F(VpiStmtCallbackByType, EveryTable38_6ObjectQualifies) {
  int suffix = 0;
  for (const StmtObject& obj : kTable386Objects) {
    std::string name = "s" + std::to_string(suffix++);
    vpiHandle stmt = MakeHandleOfType(name.c_str(), obj.type);
    ASSERT_NE(stmt, nullptr) << obj.label;

    s_cb_data cb = {};
    cb.reason = cbStmt;
    cb.obj = stmt;
    EXPECT_NE(vpi_register_cb(&cb), nullptr)
        << "Table 38-6 object '" << obj.label << "' should qualify for cbStmt";
  }
}

}  // namespace
}  // namespace delta
