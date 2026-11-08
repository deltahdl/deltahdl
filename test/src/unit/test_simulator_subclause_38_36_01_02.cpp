#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct StmtObject {
  int type;
  const char* label;
};

constexpr StmtObject kStatementClassObjects[] = {
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

  vpiHandle MakeHandleOfType(const char* name, int type) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(VpiText(name), nullptr);
    if (h) VpiObjectOf(h)->type = type;
    return h;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiStmtCallbackByType, EveryStatementClassObjectQualifies) {
  int suffix = 0;
  for (const StmtObject& obj : kStatementClassObjects) {
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

TEST_F(VpiStmtCallbackByType, ObjectOutsideTheStatementClassDoesNotQualify) {
  vpiHandle reg = MakeHandleOfType("v", vpiReg);
  ASSERT_NE(reg, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = reg;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

TEST_F(VpiStmtCallbackByType, ModuleInstanceRemainsAllowedInTheObjField) {
  vpiHandle mod = MakeHandleOfType("m", vpiModule);
  ASSERT_NE(mod, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = mod;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

}  // namespace
}  // namespace delta
