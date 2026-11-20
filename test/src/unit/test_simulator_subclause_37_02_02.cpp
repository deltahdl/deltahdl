#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleReleaseSim : public ::testing::Test {
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

TEST_F(VpiHandleReleaseSim, ReleasingHandleMarksItReleased) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_FALSE(vpi_ctx_.HandleReleased(mod));
  vpi_ctx_.ReleaseHandle(mod);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
}

TEST_F(VpiHandleReleaseSim, ReleasingOneHandleLeavesDistinctHandleUsable) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(other, mod);

  vpi_ctx_.ReleaseHandle(mod);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(other));
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(other), VpiHandleOf(mod)), 1);
}

TEST_F(VpiHandleReleaseSim, ReleasingOneHandedOutHandleLeavesTheOtherLive) {
  vpi_ctx_.CreateModule("top", "top");
  PLI_BYTE8 name[] = "top";
  vpiHandle first = vpi_handle_by_name(name, nullptr);
  vpiHandle second = vpi_handle_by_name(name, nullptr);
  ASSERT_NE(first, nullptr);

  EXPECT_EQ(vpi_release_handle(first), 1);
  EXPECT_FALSE(vpi_ctx_.HandleReleased(VpiObjectOf(second)));
  EXPECT_EQ(vpi_release_handle(second), 1);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(VpiObjectOf(second)));

  vpiHandle again = vpi_handle_by_name(name, nullptr);
  EXPECT_FALSE(vpi_ctx_.HandleReleased(VpiObjectOf(again)));
  EXPECT_EQ(vpi_release_handle(again), 1);
}

TEST_F(VpiHandleReleaseSim, ReleasingNullIsHarmlessAndReleaseIsIdempotent) {
  vpi_ctx_.ReleaseHandle(nullptr);
  EXPECT_FALSE(vpi_ctx_.HandleReleased(nullptr));

  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.ReleaseHandle(mod);
  vpi_ctx_.ReleaseHandle(mod);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
}

TEST_F(VpiHandleReleaseSim, RestartReleasesAllButRestartCallbackHandles) {
  s_cb_data start{};
  start.reason = cbStartOfRestart;
  auto* start_cb = vpi_ctx_.RegisterCb(&start);

  s_cb_data end{};
  end.reason = cbEndOfRestart;
  auto* end_cb = vpi_ctx_.RegisterCb(&end);

  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data ordinary{};
  ordinary.reason = cbValueChange;
  ordinary.obj = VpiHandleOf(&watched);
  auto* ordinary_cb = vpi_ctx_.RegisterCb(&ordinary);

  auto* mod = vpi_ctx_.CreateModule("top", "top");

  vpi_ctx_.DispatchRestart();

  EXPECT_FALSE(vpi_ctx_.HandleReleased(start_cb));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(end_cb));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(ordinary_cb));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
}

TEST_F(VpiHandleReleaseSim, DISABLED_RestartReleasesAnIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p", kVpiInput, mod);
  vpiHandle it = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(it, nullptr);

  vpi_ctx_.DispatchRestart();

  EXPECT_TRUE(vpi_ctx_.HandleReleased(VpiObjectOf(it)));
}

TEST_F(VpiHandleReleaseSim,
       DISABLED_RestartReleasesASystfBesideARestartCallback) {
  s_cb_data start{};
  start.reason = cbStartOfRestart;
  auto* start_cb = vpi_ctx_.RegisterCb(&start);

  s_vpi_systf_data data{};
  data.type = vpiSysTask;
  PLI_BYTE8 name[] = "$restarted";
  data.tfname = name;
  vpiHandle systf = vpi_register_systf(&data);
  ASSERT_NE(systf, nullptr);

  vpi_ctx_.DispatchRestart();

  EXPECT_FALSE(vpi_ctx_.HandleReleased(start_cb));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(VpiObjectOf(systf)));
}

TEST_F(VpiHandleReleaseSim, RestartReleasesAScheduledEvent) {
  auto* var = sim_ctx_.CreateVariable("re", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);
  PLI_BYTE8 name[] = "re";
  vpiHandle h = vpi_handle_by_name(name, nullptr);
  ASSERT_NE(h, nullptr);
  s_vpi_value val{};
  val.format = vpiIntVal;
  val.value.integer = 12;
  s_vpi_time time{};
  time.type = vpiSimTime;
  time.low = 5;
  vpiHandle ev =
      vpi_put_value(h, &val, &time, vpiInertialDelay | vpiReturnEvent);
  ASSERT_NE(ev, nullptr);

  vpi_ctx_.DispatchRestart();

  EXPECT_TRUE(vpi_ctx_.HandleReleased(VpiObjectOf(ev)));
}

TEST_F(VpiHandleReleaseSim, DISABLED_AScanThatRunsOutReleasesItsIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p", kVpiInput, mod);
  vpiHandle it = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(it, nullptr);
  ASSERT_NE(vpi_scan(it), nullptr);
  ASSERT_EQ(vpi_scan(it), nullptr);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(VpiObjectOf(it)));
  EXPECT_FALSE(vpi_ctx_.HandleValid(VpiObjectOf(it)));
}

TEST_F(VpiHandleReleaseSim, FreeingFrameObjectReleasesSubelementsAndCallbacks) {
  auto* frame_obj = vpi_ctx_.CreateModule("f", "f");
  auto* subelement = vpi_ctx_.CreateModule("f.s", "f.s");
  frame_obj->children.push_back(subelement);

  s_cb_data cb_data{};
  cb_data.reason = cbValueChange;
  cb_data.obj = VpiHandleOf(subelement);
  auto* cb = vpi_ctx_.RegisterCb(&cb_data);

  vpi_ctx_.ReleaseFrameOrThreadObject(frame_obj);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(frame_obj));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(subelement));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(cb));
}

TEST_F(VpiHandleReleaseSim, EndingAThreadLeavesTheThreadsItSpawnedLive) {
  auto* parent = vpi_ctx_.CreateModule("p", "p");
  auto* child = vpi_ctx_.CreateModule("c", "c");
  parent->type = vpiThread;
  child->type = vpiThread;
  parent->children.push_back(child);

  vpi_ctx_.ReleaseFrameOrThreadObject(parent);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(parent));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(child));
}

TEST_F(VpiHandleReleaseSim, ReclaimingClassObjectReleasesAutomaticNotStatic) {
  auto* class_obj = vpi_ctx_.CreateModule("obj", "obj");

  auto* automatic_member = vpi_ctx_.CreateModule("obj.a", "obj.a");
  automatic_member->automatic = true;
  auto* automatic_subelement = vpi_ctx_.CreateModule("obj.a.s", "obj.a.s");
  automatic_member->children.push_back(automatic_subelement);

  auto* static_member = vpi_ctx_.CreateModule("obj.st", "obj.st");
  static_member->automatic = false;

  auto* method = vpi_ctx_.CreateModule("C::f", "C::f");
  method->type = vpiFunction;
  method->automatic = true;

  class_obj->children.push_back(automatic_member);
  class_obj->children.push_back(static_member);
  class_obj->children.push_back(method);

  s_cb_data cb_data{};
  cb_data.reason = cbStmt;
  cb_data.obj = VpiHandleOf(automatic_member);
  auto* cb = vpi_ctx_.RegisterCb(&cb_data);

  vpi_ctx_.ReleaseClassObject(class_obj);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(class_obj));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(automatic_member));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(automatic_subelement));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(cb));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(static_member));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(method));
}

TEST_F(VpiHandleReleaseSim, ReclaimingClassObjectKeepsAClassVarsClassDefn) {
  auto* class_obj = vpi_ctx_.CreateModule("obj", "obj");
  auto* class_var = vpi_ctx_.CreateModule("obj.b", "obj.b");
  class_var->type = vpiClassVar;
  class_var->automatic = true;
  auto* typespec = vpi_ctx_.CreateModule("B", "B");
  typespec->type = vpiClassTypespec;
  auto* defn = vpi_ctx_.CreateModule("B", "B");
  defn->type = vpiClassDefn;
  typespec->children.push_back(defn);
  class_var->children.push_back(typespec);
  class_obj->children.push_back(class_var);

  vpi_ctx_.ReleaseClassObject(class_obj);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(class_var));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(typespec));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(defn));
}

TEST_F(VpiHandleReleaseSim, RemovingACallbackReleasesItsHandle) {
  s_cb_data data = {};
  data.reason = cbEndOfSimulation;
  data.cb_rtn = nullptr;
  vpiHandle cb = vpi_register_cb(&data);
  ASSERT_NE(cb, nullptr);
  EXPECT_FALSE(VpiObjectOf(cb)->released);

  EXPECT_EQ(vpi_remove_cb(cb), 1);
  EXPECT_TRUE(VpiObjectOf(cb)->released);

  EXPECT_EQ(vpi_remove_cb(cb), 0);
}

TEST_F(VpiHandleReleaseSim, RemovingOneCallbackLeavesAnotherHandleLive) {
  s_cb_data first = {};
  first.reason = cbEndOfSimulation;
  vpiHandle removed = vpi_register_cb(&first);
  ASSERT_NE(removed, nullptr);

  s_cb_data second = {};
  second.reason = cbEndOfSimulation;
  vpiHandle kept = vpi_register_cb(&second);
  ASSERT_NE(kept, nullptr);

  EXPECT_EQ(vpi_remove_cb(removed), 1);

  EXPECT_TRUE(VpiObjectOf(removed)->released);
  EXPECT_FALSE(VpiObjectOf(kept)->released);
}

struct GrabbedHandles {
  vpiHandle frame = nullptr;
  vpiHandle thread = nullptr;
  vpiHandle automatic = nullptr;
  vpiHandle static_local = nullptr;
  vpiHandle object = nullptr;
  vpiHandle member = nullptr;
  vpiHandle static_member = nullptr;
  vpiHandle callback = nullptr;
};
GrabbedHandles g_grabbed;

PLI_INT32 NoteCallback(s_cb_data*) { return 0; }

vpiHandle PlaceCallback(int reason, vpiHandle on) {
  s_cb_data data{};
  data.reason = reason;
  data.cb_rtn = &NoteCallback;
  data.obj = on;
  return vpi_register_cb(&data);
}

PLI_INT32 GrabFrameCalltf(PLI_BYTE8*) {
  g_grabbed.frame = vpi_handle(vpiFrame, nullptr);
  if (g_grabbed.frame == nullptr) return 0;
  g_grabbed.thread = vpi_handle(vpiThread, g_grabbed.frame);
  vpiHandle it = vpi_iterate(vpiAutomatics, g_grabbed.frame);
  g_grabbed.automatic = it == nullptr ? nullptr : vpi_scan(it);
  if (g_grabbed.automatic != nullptr) vpi_release_handle(it);
  g_grabbed.static_local = vpi_handle_by_name(VpiText("t.tk.s"), nullptr);
  g_grabbed.callback = PlaceCallback(cbEndOfFrame, g_grabbed.frame);
  return 0;
}

PLI_INT32 GrabObjectCalltf(PLI_BYTE8*) {
  g_grabbed.object =
      vpi_handle(vpiClassObj, vpi_handle_by_name(VpiText("t.c"), nullptr));
  vpiHandle it = vpi_iterate(vpiVariables, g_grabbed.object);
  while (vpiHandle var = it == nullptr ? nullptr : vpi_scan(it)) {
    const std::string kName = vpi_get_str(vpiName, var);
    if (kName == "x") g_grabbed.member = var;
    if (kName == "s") g_grabbed.static_member = var;
  }
  return 0;
}

class HandleReleaseInARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_grabbed = {};
    Register("$grab_frame", &GrabFrameCalltf);
    Register("$grab_object", &GrabObjectCalltf);
  }

  static void Register(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data{};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  void RunTaskWithLocals() {
    Run("module t;\n"
        "  task automatic tk();\n"
        "    int x;\n"
        "    static int s;\n"
        "    $grab_frame;\n"
        "  endtask\n"
        "  initial tk();\n"
        "endmodule\n");
  }

  bool Released(vpiHandle handle) const {
    return vpi_.HandleReleased(VpiObjectOf(handle));
  }
};

TEST_F(HandleReleaseInARun, AReturningTaskReleasesItsFrameAndItsCallbacks) {
  RunTaskWithLocals();

  ASSERT_NE(g_grabbed.frame, nullptr);
  ASSERT_NE(g_grabbed.callback, nullptr);
  EXPECT_TRUE(Released(g_grabbed.frame));
  EXPECT_TRUE(Released(g_grabbed.callback));
}

TEST_F(HandleReleaseInARun, DISABLED_AReturningTaskReleasesItsAutomatics) {
  RunTaskWithLocals();

  ASSERT_NE(g_grabbed.automatic, nullptr);
  EXPECT_TRUE(Released(g_grabbed.automatic));
}

TEST_F(HandleReleaseInARun, AReturningTaskKeepsItsStaticLocal) {
  RunTaskWithLocals();

  ASSERT_NE(g_grabbed.static_local, nullptr);
  EXPECT_FALSE(Released(g_grabbed.static_local));
}

TEST_F(HandleReleaseInARun, AnEndingThreadReleasesItsHandle) {
  Run("module t;\n"
      "  task automatic tk();\n"
      "    $grab_frame;\n"
      "  endtask\n"
      "  initial tk();\n"
      "endmodule\n");

  ASSERT_NE(g_grabbed.thread, nullptr);
  EXPECT_TRUE(Released(g_grabbed.thread));
}

TEST_F(HandleReleaseInARun, ReclaimingAnObjectReleasesItsAutomaticMembers) {
  Run("module t;\n"
      "  class C;\n"
      "    int x;\n"
      "    static int s;\n"
      "  endclass\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    $grab_object;\n"
      "    c = null;\n"
      "  end\n"
      "endmodule\n");
  f_.ctx.CollectGarbage();

  ASSERT_NE(g_grabbed.object, nullptr);
  ASSERT_NE(g_grabbed.member, nullptr);
  ASSERT_NE(g_grabbed.static_member, nullptr);
  EXPECT_TRUE(Released(g_grabbed.object));
  EXPECT_TRUE(Released(g_grabbed.member));
  EXPECT_FALSE(Released(g_grabbed.static_member));
}

}  // namespace
}  // namespace delta
