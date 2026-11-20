#include <gtest/gtest.h>

#include <cstdarg>
#include <cstddef>
#include <functional>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

extern "C" {
vpiHandle vpi_iterate_1364v1995(PLI_INT32 type, vpiHandle ref);
vpiHandle vpi_iterate_1800v2012(PLI_INT32 type, vpiHandle ref);
}

namespace delta {
namespace {

VpiToolPhase g_phase_during_routine = VpiToolPhase::kFull;
bool g_routine_systf_registered = false;
bool g_routine_allowed_cb_registered = false;
bool g_routine_illegal_cb_registered = false;

int NoopCb(s_cb_data*) { return 0; }

void StartupRoutine() {
  g_phase_during_routine = GetGlobalVpiContext().ToolPhase();

  s_vpi_systf_data systf = {};
  systf.type = vpiSysTask;
  systf.tfname = VpiText("$my_task");
  g_routine_systf_registered = vpi_register_systf(&systf) != nullptr;

  s_cb_data ok = {};
  ok.reason = cbEndOfCompile;
  ok.cb_rtn = NoopCb;
  g_routine_allowed_cb_registered = vpi_register_cb(&ok) != nullptr;

  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data bad = {};
  bad.reason = cbValueChange;
  bad.cb_rtn = NoopCb;
  bad.obj = VpiHandleOf(&watched);
  g_routine_illegal_cb_registered = vpi_register_cb(&bad) != nullptr;
}

class VpiFunctionAvailability : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiFunctionAvailability, OnlyRegistrationRoutinesAvailableInStartup) {
  EXPECT_TRUE(VpiRoutineAvailableInStartup(VpiRoutine::kRegisterSystf));
  EXPECT_TRUE(VpiRoutineAvailableInStartup(VpiRoutine::kRegisterCb));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kGetValue));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kPutValue));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kIterate));
}

TEST_F(VpiFunctionAvailability, OnlyFullPhaseIsUnrestricted) {
  EXPECT_TRUE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kStartup));
  EXPECT_TRUE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kSizetf));
  EXPECT_FALSE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kFull));
}

TEST_F(VpiFunctionAvailability, StartupCallbackReasonSetIsTheSixReasons) {
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbEndOfCompile));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbStartOfSimulation));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbEndOfSimulation));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbUnresolvedSystf));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbError));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbPLIError));

  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbValueChange));
  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbReadWriteSynch));
  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbStmt));
  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbAfterDelay));
}

TEST_F(VpiFunctionAvailability, RegisterCbAcceptsEarlyReasonsInStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  const int kReasons[] = {cbEndOfCompile,    cbStartOfSimulation,
                          cbEndOfSimulation, cbUnresolvedSystf,
                          cbError,           cbPLIError};
  for (int reason : kReasons) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = NoopCb;
    EXPECT_NE(vpi_register_cb(&cb), nullptr) << "reason " << reason;
  }
}

TEST_F(VpiFunctionAvailability, RegisterCbRejectsOtherReasonInStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  size_t before = vpi_ctx_.RegisteredCallbacks().size();

  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = NoopCb;
  cb.obj = VpiHandleOf(&watched);
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().size(), before);
  EXPECT_EQ(vpi_ctx_.LastError().level, vpiError);
}

TEST_F(VpiFunctionAvailability, RegisterCbRejectsOtherReasonInSizetfPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kSizetf);
  VpiObject stmt;
  stmt.type = vpiAssignment;
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = NoopCb;
  cb.obj = VpiHandleOf(&stmt);
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiFunctionAvailability, RegisterCbAcceptsAnyReasonInFullPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = NoopCb;
  cb.obj = VpiHandleOf(&watched);
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiFunctionAvailability, StartupWalkEstablishesAndRestoresPhase) {
  g_phase_during_routine = VpiToolPhase::kFull;
  g_routine_systf_registered = false;
  g_routine_allowed_cb_registered = false;
  g_routine_illegal_cb_registered = false;

  VlogStartupRoutine routines[] = {&StartupRoutine, nullptr};
  InvokeVlogStartupRoutines(routines);

  EXPECT_EQ(g_phase_during_routine, VpiToolPhase::kStartup);
  EXPECT_TRUE(g_routine_systf_registered);
  EXPECT_TRUE(g_routine_allowed_cb_registered);
  EXPECT_FALSE(g_routine_illegal_cb_registered);
  EXPECT_EQ(vpi_ctx_.ToolPhase(), VpiToolPhase::kFull);
}

TEST_F(VpiFunctionAvailability, IterateIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_STREQ(info.message,
               "VPI routine is not available until cbEndOfCompile; only "
               "vpi_register_systf() and vpi_register_cb() may be called "
               "before then");
}

TEST_F(VpiFunctionAvailability, IterateIsRefusedDuringTheSizetfPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kSizetf);

  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiFunctionAvailability, TheFullPhaseRefusesNothingAndStartupSparesTwo) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kIterate));
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kGetValue));
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kPutValue));

  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kRegisterSystf));
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kRegisterCb));
  EXPECT_TRUE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kIterate));
}

TEST_F(VpiFunctionAvailability, GetValueIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 4321;
  vpi_get_value(nullptr, &value);

  EXPECT_EQ(value.value.integer, 4321);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiFunctionAvailability, PutValueIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;
  EXPECT_EQ(vpi_put_value(nullptr, &value, nullptr, vpiNoDelay), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiFunctionAvailability,
       ACompatibilityModeIterateIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  EXPECT_EQ(vpi_iterate_1364v1995(vpiModule, nullptr), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
  vpi_ctx_.ResetErrorStatus();
  EXPECT_EQ(vpi_iterate_1800v2012(vpiModule, nullptr), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

PLI_INT32 PrintThroughAList(const char* format, ...) {
  va_list ap{};
  va_start(ap, format);
  const PLI_INT32 kWritten = vpi_vprintf(const_cast<PLI_BYTE8*>(format), ap);
  va_end(ap);
  return kWritten;
}

vpiHandle g_kept_call = nullptr;

PLI_INT32 KeepTheCall(PLI_BYTE8*) {
  g_kept_call = vpi_handle(vpiSysTfCall, nullptr);
  return 0;
}

PLI_INT32 PrintToAnMcdThroughAList(PLI_UINT32 mcd, const char* format, ...) {
  va_list args{};
  va_start(args, format);
  const PLI_INT32 kWritten = vpi_mcd_vprintf(mcd, VpiText(format), args);
  va_end(args);
  return kWritten;
}

class AvailabilityInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void RunTheDesign() {
    s_vpi_systf_data keep = {};
    keep.type = vpiSysTask;
    keep.tfname = VpiText("$keep");
    keep.calltf = KeepTheCall;
    ASSERT_NE(vpi_register_systf(&keep), nullptr);
    s_cb_data attach = {};
    attach.reason = cbEndOfSimulation;
    attach.cb_rtn = NoopCb;
    ASSERT_NE(vpi_register_cb(&attach), nullptr);
    auto* design = ElaborateSrc(
        "module t;\n"
        "  int r = 5;\n"
        "  int a [2];\n"
        "  wire w;\n"
        "  assign #3 w = 1'b1;\n"
        "  initial $keep;\n"
        "endmodule\n",
        f_);
    ASSERT_NE(design, nullptr);
    LowerAndRun(design, f_);
    r_ = vpi_handle_by_name(VpiText("t.r"), nullptr);
    a_ = vpi_handle_by_name(VpiText("t.a"), nullptr);
    ASSERT_NE(r_, nullptr);
    ASSERT_NE(a_, nullptr);
    vpiHandle assigns =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("t"), nullptr));
    ASSERT_NE(assigns, nullptr);
    assign_ = vpi_scan(assigns);
    ASSERT_NE(assign_, nullptr);
    ASSERT_NE(g_kept_call, nullptr);
  }

  void ExpectRefusedOnlyDuringStartup(const char* routine,
                                      const std::function<void()>& call) {
    SCOPED_TRACE(routine);
    vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
    vpi_ctx_.ResetErrorStatus();
    call();
    const PLI_INT32 kDuringStartup = vpi_chk_error(nullptr);
    EXPECT_EQ(kDuringStartup, vpiError);
    vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
    vpi_ctx_.ResetErrorStatus();
    call();
    const PLI_INT32 kAfterwards = vpi_chk_error(nullptr);
    EXPECT_LT(kAfterwards, vpiError);
  }

  VpiContext vpi_ctx_;
  SimFixture f_;
  vpiHandle r_ = nullptr;
  vpiHandle a_ = nullptr;
  vpiHandle assign_ = nullptr;
};

TEST_F(AvailabilityInARun, ValueAccessToALiveObjectWaitsForTheFullPhase) {
  RunTheDesign();
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  s_vpi_value got = {};
  got.format = vpiIntVal;
  got.value.integer = 4321;
  vpi_get_value(r_, &got);
  const PLI_INT32 kGetRefused = vpi_chk_error(nullptr);
  s_vpi_value put = {};
  put.format = vpiIntVal;
  put.value.integer = 9;
  vpi_put_value(r_, &put, nullptr, vpiNoDelay);
  const PLI_INT32 kPutRefused = vpi_chk_error(nullptr);
  EXPECT_EQ(got.value.integer, 4321);
  EXPECT_NE(kGetRefused, 0);
  EXPECT_NE(kPutRefused, 0);
  EXPECT_EQ(f_.ctx.FindVariable("r")->value.ToUint64(), 5U);

  vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
  vpi_ctx_.ResetErrorStatus();
  vpi_get_value(r_, &got);
  EXPECT_EQ(got.value.integer, 5);
  vpi_put_value(r_, &put, nullptr, vpiNoDelay);
  const PLI_INT32 kFullError = vpi_chk_error(nullptr);
  EXPECT_EQ(kFullError, 0);
  EXPECT_EQ(f_.ctx.FindVariable("r")->value.ToUint64(), 9U);
}

TEST_F(AvailabilityInARun, DISABLED_HandleRoutinesAreRefusedDuringStartup) {
  RunTheDesign();
  ExpectRefusedOnlyDuringStartup("vpi_handle",
                                 [&] { vpi_handle(vpiModule, r_); });
  ExpectRefusedOnlyDuringStartup("vpi_handle_by_name", [&] {
    vpi_handle_by_name(VpiText("t.r"), nullptr);
  });
  ExpectRefusedOnlyDuringStartup("vpi_handle_by_index",
                                 [&] { vpi_handle_by_index(a_, 0); });
  ExpectRefusedOnlyDuringStartup("vpi_handle_by_multi_index", [&] {
    PLI_INT32 index[] = {1};
    vpi_handle_by_multi_index(a_, 1, index);
  });
  vpiHandle module = vpi_handle(vpiModule, r_);
  vpiHandle iterators[] = {vpi_iterate(vpiVariables, module),
                           vpi_iterate(vpiVariables, module)};
  ASSERT_NE(iterators[0], nullptr);
  ASSERT_NE(iterators[1], nullptr);
  int next = 0;
  ExpectRefusedOnlyDuringStartup("vpi_scan",
                                 [&] { vpi_scan(iterators[next++]); });
}

TEST_F(AvailabilityInARun,
       DISABLED_PropertyAndTimeRoutinesAreRefusedDuringStartup) {
  RunTheDesign();
  ExpectRefusedOnlyDuringStartup("vpi_get", [&] { vpi_get(vpiSize, r_); });
  ExpectRefusedOnlyDuringStartup("vpi_get64", [&] { vpi_get64(vpiSize, r_); });
  ExpectRefusedOnlyDuringStartup("vpi_get_str",
                                 [&] { vpi_get_str(vpiName, r_); });
  ExpectRefusedOnlyDuringStartup("vpi_get_time", [&] {
    s_vpi_time now = {};
    now.type = vpiSimTime;
    vpi_get_time(nullptr, &now);
  });
  ExpectRefusedOnlyDuringStartup("vpi_compare_objects",
                                 [&] { vpi_compare_objects(r_, r_); });
}

TEST_F(AvailabilityInARun, DISABLED_ArrayValueRoutinesAreRefusedDuringStartup) {
  RunTheDesign();
  ExpectRefusedOnlyDuringStartup("vpi_get_value_array", [&] {
    PLI_INT32 words[2] = {};
    s_vpi_arrayvalue values = {};
    values.format = vpiIntVal;
    values.value.integers = words;
    PLI_INT32 index[] = {0};
    vpi_get_value_array(a_, &values, index, 2);
  });
  ExpectRefusedOnlyDuringStartup("vpi_put_value_array", [&] {
    PLI_INT32 words[2] = {3, 4};
    s_vpi_arrayvalue values = {};
    values.format = vpiIntVal;
    values.value.integers = words;
    PLI_INT32 index[] = {0};
    vpi_put_value_array(a_, &values, index, 2);
  });
}

TEST_F(AvailabilityInARun,
       DISABLED_CallbackAndSystfQueriesAreRefusedDuringStartup) {
  RunTheDesign();
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = NoopCb;
  vpiHandle first = vpi_register_cb(&cb);
  vpiHandle second = vpi_register_cb(&cb);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$known");
  vpiHandle systf = vpi_register_systf(&task);
  ASSERT_NE(systf, nullptr);
  ExpectRefusedOnlyDuringStartup("vpi_get_cb_info", [&] {
    s_cb_data info = {};
    vpi_get_cb_info(first, &info);
  });
  ExpectRefusedOnlyDuringStartup("vpi_get_systf_info", [&] {
    s_vpi_systf_data info = {};
    vpi_get_systf_info(systf, &info);
  });
  vpiHandle removable = first;
  ExpectRefusedOnlyDuringStartup("vpi_remove_cb", [&] {
    vpi_remove_cb(removable);
    removable = second;
  });
}

TEST_F(AvailabilityInARun, DISABLED_ReleaseRoutinesAreRefusedDuringStartup) {
  RunTheDesign();
  vpiHandle module = vpi_handle(vpiModule, r_);
  vpiHandle freed[] = {vpi_iterate(vpiVariables, module),
                       vpi_iterate(vpiVariables, module)};
  vpiHandle released[] = {vpi_handle_by_name(VpiText("t.a"), nullptr),
                          vpi_handle_by_name(VpiText("t.a"), nullptr)};
  int next_freed = 0;
  int next_released = 0;
  ExpectRefusedOnlyDuringStartup("vpi_free_object",
                                 [&] { vpi_free_object(freed[next_freed++]); });
  ExpectRefusedOnlyDuringStartup("vpi_release_handle", [&] {
    vpi_release_handle(released[next_released++]);
  });
}

TEST_F(AvailabilityInARun,
       DISABLED_PrintingAndInfoRoutinesAreRefusedDuringStartup) {
  RunTheDesign();
  ExpectRefusedOnlyDuringStartup("vpi_printf",
                                 [] { vpi_printf(VpiText("%s"), ""); });
  ExpectRefusedOnlyDuringStartup("vpi_vprintf",
                                 [] { PrintThroughAList("%s", ""); });
  ExpectRefusedOnlyDuringStartup("vpi_mcd_printf",
                                 [] { vpi_mcd_printf(1, VpiText("%s"), ""); });
  ExpectRefusedOnlyDuringStartup("vpi_mcd_name", [] { vpi_mcd_name(1); });
  ExpectRefusedOnlyDuringStartup("vpi_mcd_flush", [] { vpi_mcd_flush(1); });
  ExpectRefusedOnlyDuringStartup("vpi_flush", [] { vpi_flush(); });
  ExpectRefusedOnlyDuringStartup("vpi_get_vlog_info", [] {
    s_vpi_vlog_info info = {};
    vpi_get_vlog_info(&info);
  });
}

TEST_F(AvailabilityInARun,
       DISABLED_DelayAndUserDataRoutinesAreRefusedDuringStartup) {
  RunTheDesign();
  ExpectRefusedOnlyDuringStartup("vpi_get_delays", [this] {
    s_vpi_time times[2] = {};
    times[0].type = vpiSimTime;
    times[1].type = vpiSimTime;
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiSimTime;
    vpi_get_delays(assign_, &delay);
  });
  ExpectRefusedOnlyDuringStartup("vpi_put_delays", [this] {
    s_vpi_time times[2] = {};
    times[0].type = vpiSimTime;
    times[0].low = 3;
    times[1].type = vpiSimTime;
    times[1].low = 3;
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiSimTime;
    vpi_put_delays(assign_, &delay);
  });
  int marker = 0;
  ExpectRefusedOnlyDuringStartup("vpi_put_userdata", [&marker] {
    vpi_put_userdata(g_kept_call, &marker);
  });
  ExpectRefusedOnlyDuringStartup("vpi_get_userdata",
                                 [] { vpi_get_userdata(g_kept_call); });
  ExpectRefusedOnlyDuringStartup("vpi_handle_multi", [this] {
    vpi_handle_multi(vpiInterModPath, r_, r_);
  });
}

TEST_F(AvailabilityInARun,
       DISABLED_ControlAndFileRoutinesAreRefusedDuringStartup) {
  RunTheDesign();
  ExpectRefusedOnlyDuringStartup("vpi_control", [] {
    vpi_control(vpiSetInteractiveScope,
                vpi_handle_by_name(VpiText("t"), nullptr));
  });
  const std::string kPath = ::testing::TempDir() + "availability_36_10_2.log";
  std::vector<PLI_UINT32> opened;
  ExpectRefusedOnlyDuringStartup("vpi_mcd_open", [&kPath, &opened] {
    opened.push_back(vpi_mcd_open(VpiText(kPath.c_str())));
  });
  vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
  const PLI_UINT32 kMcd = vpi_mcd_open(VpiText(kPath.c_str()));
  ASSERT_NE(kMcd, 0U);
  ExpectRefusedOnlyDuringStartup(
      "vpi_mcd_vprintf", [kMcd] { PrintToAnMcdThroughAList(kMcd, "%s", ""); });
  ExpectRefusedOnlyDuringStartup("vpi_mcd_close",
                                 [kMcd] { vpi_mcd_close(kMcd); });
  for (const PLI_UINT32 kOpened : opened) {
    if (kOpened != 0 && kOpened != kMcd) vpi_mcd_close(kOpened);
  }
}

bool g_startup_iterate_refused = false;

void StartupRoutineIterates() {
  vpiHandle it = vpi_iterate(vpiModule, nullptr);
  const PLI_INT32 kError = vpi_chk_error(nullptr);
  g_startup_iterate_refused = it == nullptr && kError != 0;
}

TEST_F(VpiFunctionAvailability, AnIterateInsideAStartupRoutineIsRefused) {
  g_startup_iterate_refused = false;
  VlogStartupRoutine routines[] = {&StartupRoutineIterates, nullptr};
  InvokeVlogStartupRoutines(routines);
  EXPECT_TRUE(g_startup_iterate_refused);
}

TEST_F(VpiFunctionAvailability, EveryOtherReasonIsRefusedDuringStartup) {
  const int kLateReasons[] = {
      cbValueChange,
      cbStmt,
      cbForce,
      cbRelease,
      cbAtStartOfSimTime,
      cbReadWriteSynch,
      cbReadOnlySynch,
      cbNextSimTime,
      cbAfterDelay,
      cbTchkViolation,
      cbStartOfSave,
      cbEndOfSave,
      cbStartOfRestart,
      cbEndOfRestart,
      cbStartOfReset,
      cbEndOfReset,
      cbEnterInteractive,
      cbExitInteractive,
      cbInteractiveScopeChange,
      cbAssign,
      cbDeassign,
      cbDisable,
      cbSignal,
      cbNBASynch,
      cbAtEndOfSimTime,
  };
  VpiObject watched;
  watched.type = vpiReg;
  s_vpi_time when = {};
  when.type = vpiSimTime;
  when.low = 1;
  for (int reason : kLateReasons) {
    SCOPED_TRACE(reason);
    vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
    vpi_ctx_.ResetErrorStatus();
    const size_t kBefore = vpi_ctx_.RegisteredCallbacks().size();
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = NoopCb;
    cb.obj = VpiHandleOf(&watched);
    cb.time = &when;
    EXPECT_EQ(vpi_register_cb(&cb), nullptr);
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    EXPECT_EQ(kLevel, vpiError);
    EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().size(), kBefore);
  }
}

bool g_sizetf_iterate_refused = false;
bool g_sizetf_early_cb_accepted = false;
bool g_sizetf_late_cb_refused = false;
bool g_early_cb_ran = false;
bool g_compile_iterate_found_top = false;
PLI_INT32 g_compile_error = -1;

int MarkTheEarlyCallbackRan(s_cb_data*) {
  g_early_cb_ran = true;
  return 0;
}

PLI_INT32 ReachingSizetf(PLI_BYTE8*) {
  vpiHandle it = vpi_iterate(vpiModule, nullptr);
  const PLI_INT32 kIterateError = vpi_chk_error(nullptr);
  g_sizetf_iterate_refused = it == nullptr && kIterateError != 0;

  s_cb_data early = {};
  early.reason = cbEndOfCompile;
  early.cb_rtn = MarkTheEarlyCallbackRan;
  g_sizetf_early_cb_accepted = vpi_register_cb(&early) != nullptr;

  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data late = {};
  late.reason = cbValueChange;
  late.cb_rtn = NoopCb;
  late.obj = VpiHandleOf(&watched);
  vpiHandle late_handle = vpi_register_cb(&late);
  const PLI_INT32 kLateError = vpi_chk_error(nullptr);
  g_sizetf_late_cb_refused = late_handle == nullptr && kLateError != 0;
  return 32;
}

int IterateAtTheEndOfCompile(s_cb_data*) {
  vpiHandle it = vpi_iterate(vpiModule, nullptr);
  vpiHandle top = it == nullptr ? nullptr : vpi_scan(it);
  g_compile_iterate_found_top =
      top != nullptr && std::string(vpi_get_str(vpiName, top) == nullptr
                                        ? ""
                                        : vpi_get_str(vpiName, top)) == "t";
  g_compile_error = vpi_chk_error(nullptr);
  if (it != nullptr && top != nullptr) vpi_free_object(it);
  return 0;
}

TEST_F(AvailabilityInARun, ASizetfTheToolCallsRunsUnderTheStartupLimits) {
  g_sizetf_iterate_refused = false;
  g_sizetf_early_cb_accepted = false;
  g_sizetf_late_cb_refused = false;
  g_early_cb_ran = false;
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiSizedFunc;
  data.tfname = VpiText("$sized");
  data.sizetf = &ReachingSizetf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $sized();\n"
      "endmodule\n",
      f_);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f_);
  EXPECT_TRUE(g_sizetf_iterate_refused);
  EXPECT_TRUE(g_sizetf_early_cb_accepted);
  EXPECT_TRUE(g_sizetf_late_cb_refused);
  EXPECT_TRUE(g_early_cb_ran);
}

TEST_F(AvailabilityInARun, AnEndOfCompileCallbackReachesTheWholeInterface) {
  g_compile_iterate_found_top = false;
  g_compile_error = -1;
  s_cb_data cb = {};
  cb.reason = cbEndOfCompile;
  cb.cb_rtn = IterateAtTheEndOfCompile;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "endmodule\n",
      f_);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f_);
  EXPECT_TRUE(g_compile_iterate_found_top);
  EXPECT_EQ(g_compile_error, 0);
}

}  // namespace
}  // namespace delta
