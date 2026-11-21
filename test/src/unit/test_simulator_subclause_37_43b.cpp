#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct FrameView {
  bool found = false;
  int origin_type = 0;
  std::string origin;
  int active = -1;
  std::vector<std::string> automatics;
  std::vector<bool> watchable;
  bool named_watchable = false;
  bool named_found = false;
  int parent_active = -1;
  int parent_stmt_type = 0;
  std::string parent_stmt;
  std::vector<std::string> parent_automatics;
};

std::vector<FrameView> g_views;
std::string g_watch_name;
std::string g_put_name;

PLI_INT32 IgnoreChange(p_cb_data) { return 0; }

bool Watchable(vpiHandle obj) {
  s_vpi_time time = {};
  time.type = vpiSimTime;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  s_cb_data data = {};
  data.reason = cbValueChange;
  data.cb_rtn = &IgnoreChange;
  data.obj = obj;
  data.time = &time;
  data.value = &value;
  vpiHandle cb = obj == nullptr ? nullptr : vpi_register_cb(&data);
  if (cb == nullptr) return false;
  vpi_remove_cb(cb);
  return true;
}

std::string NameOf(vpiHandle obj) {
  if (obj == nullptr) return "";
  for (const int kRelation : {vpiTask, vpiFunction}) {
    vpiHandle callee = vpi_handle(kRelation, obj);
    if (callee != nullptr) return vpi_get_str(vpiName, callee);
  }
  const char* full = vpi_get_str(vpiFullName, obj);
  return full == nullptr ? "" : full;
}

std::vector<vpiHandle> AutomaticsOf(vpiHandle frame) {
  std::vector<vpiHandle> objects;
  vpiHandle it = vpi_iterate(vpiAutomatics, frame);
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    objects.push_back(obj);
  }
  return objects;
}

std::vector<std::string> SortedNames(const std::vector<vpiHandle>& objects) {
  std::vector<std::string> names;
  names.reserve(objects.size());
  for (vpiHandle obj : objects) names.emplace_back(vpi_get_str(vpiName, obj));
  std::ranges::sort(names);
  return names;
}

void LookAtParent(vpiHandle frame, FrameView& view) {
  vpiHandle parent = vpi_handle(vpiParent, frame);
  if (parent == nullptr) return;
  view.parent_active = vpi_get(vpiActive, parent);
  vpiHandle stmt = vpi_handle(vpiStmt, parent);
  view.parent_stmt_type = stmt == nullptr ? 0 : vpi_get(vpiType, stmt);
  view.parent_stmt = NameOf(stmt);
  view.parent_automatics = SortedNames(AutomaticsOf(parent));
}

PLI_INT32 LookAtFrameCalltf(PLI_BYTE8*) {
  FrameView view;
  if (!g_watch_name.empty()) {
    vpiHandle named =
        vpi_handle_by_name(VpiText(g_watch_name.c_str()), nullptr);
    view.named_found = named != nullptr;
    view.named_watchable = Watchable(named);
  }
  vpiHandle frame = vpi_handle(vpiFrame, nullptr);
  if (frame != nullptr) {
    view.found = true;
    vpiHandle origin = vpi_handle(vpiOrigin, frame);
    view.origin_type = origin == nullptr ? 0 : vpi_get(vpiType, origin);
    view.origin = NameOf(origin);
    view.active = vpi_get(vpiActive, frame);
    const std::vector<vpiHandle> kAutomatics = AutomaticsOf(frame);
    view.automatics = SortedNames(kAutomatics);
    for (vpiHandle obj : kAutomatics) view.watchable.push_back(Watchable(obj));
    LookAtParent(frame, view);
  }
  g_views.push_back(view);
  return 0;
}

struct AutomaticPut {
  bool reached = false;
  int delayed_error = -1;
  int undelayed_error = -1;
  int value = 0;
};

AutomaticPut g_put;

PLI_INT32 PutOnAnAutomaticCalltf(PLI_BYTE8*) {
  vpiHandle frame = vpi_handle(vpiFrame, nullptr);
  const std::vector<vpiHandle> kAutomatics =
      frame == nullptr ? std::vector<vpiHandle>{} : AutomaticsOf(frame);
  vpiHandle var =
      g_put_name.empty()
          ? (kAutomatics.empty() ? nullptr : kAutomatics[0])
          : vpi_handle_by_name(VpiText(g_put_name.c_str()), nullptr);
  if (var == nullptr) return 0;
  g_put.reached = true;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 7;
  s_vpi_time delay = {};
  delay.type = vpiSimTime;
  delay.low = 5;
  vpi_put_value(var, &value, &delay, vpiTransportDelay);
  const int kDelayedError = vpi_chk_error(nullptr);
  g_put.delayed_error = kDelayedError;
  value.value.integer = 9;
  vpi_put_value(var, &value, nullptr, vpiNoDelay);
  const int kUndelayedError = vpi_chk_error(nullptr);
  g_put.undelayed_error = kUndelayedError;
  s_vpi_value read = {};
  read.format = vpiIntVal;
  vpi_get_value(var, &read);
  g_put.value = read.value.integer;
  return 0;
}

class FramesOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_views.clear();
    g_watch_name.clear();
    g_put_name.clear();
    g_put = AutomaticPut();
    for (const auto& [name, calltf] :
         {std::pair{"$frame", &LookAtFrameCalltf},
          std::pair{"$putauto", &PutOnAnAutomaticCalltf}}) {
      s_vpi_systf_data data = {};
      data.type = vpiSysTask;
      data.tfname = VpiText(name);
      data.calltf = calltf;
      ASSERT_NE(vpi_register_systf(&data), nullptr);
    }
  }

  static const FrameView& OnlyView() {
    EXPECT_EQ(g_views.size(), 1U);
    static const FrameView kNone;
    return g_views.empty() ? kNone : g_views[0];
  }
};

constexpr const char* kMethodFrames =
    "class C;\n"
    "  task t(); int a; event e; $frame; endtask\n"
    "  function int f(); int b; $frame; return 1; endfunction\n"
    "endclass\n"
    "module top; C o = new; int r;\n"
    "  initial begin o.t(); r = o.f(); end\n"
    "endmodule\n";

TEST_F(FramesOfARun, AClassTaskMethodCallActivatesAFrame) {
  Run(kMethodFrames);
  ASSERT_EQ(g_views.size(), 2U);
  EXPECT_TRUE(g_views[0].found);
  EXPECT_EQ(g_views[0].active, 1);
  EXPECT_EQ(g_views[0].origin_type, vpiMethodTaskCall);
  EXPECT_EQ(g_views[0].origin, "t");
  EXPECT_EQ(g_views[0].automatics, (std::vector<std::string>{"a", "e"}));
}

TEST_F(FramesOfARun, AClassFunctionMethodCallActivatesAFrame) {
  Run(kMethodFrames);
  ASSERT_EQ(g_views.size(), 2U);
  EXPECT_TRUE(g_views[1].found);
  EXPECT_EQ(g_views[1].active, 1);
  EXPECT_EQ(g_views[1].origin_type, vpiMethodFuncCall);
  EXPECT_EQ(g_views[1].origin, "f");
  EXPECT_EQ(g_views[1].automatics, std::vector<std::string>{"b"});
}

constexpr const char* kElementSubroutines =
    "package pk; task automatic pt(); int p1; $frame; endtask endpackage\n"
    "interface ifc;\n"
    "  function automatic int itf(); int i1; $frame; return 1; endfunction\n"
    "endinterface\n"
    "program pg; task automatic prt(); int r1; $frame; endtask\n"
    "  initial prt();\n"
    "endprogram\n"
    "module top; ifc i(); pg p(); int r;\n"
    "  initial begin pk::pt(); r = i.itf(); end\n"
    "endmodule\n";

bool AFrameHoldsLocal(const std::string& local) {
  return std::ranges::any_of(g_views, [&](const FrameView& view) {
    return view.found && view.active == 1 &&
           view.automatics == std::vector<std::string>{local};
  });
}

TEST_F(FramesOfARun, APackageTaskActivatesAFrame) {
  Run(kElementSubroutines);
  EXPECT_EQ(g_views.size(), 3U);
  EXPECT_TRUE(AFrameHoldsLocal("p1"));
}

TEST_F(FramesOfARun, AProgramTaskActivatesAFrame) {
  Run(kElementSubroutines);
  EXPECT_EQ(g_views.size(), 3U);
  EXPECT_TRUE(AFrameHoldsLocal("r1"));
}

TEST_F(FramesOfARun, DISABLED_AnInterfaceFunctionActivatesAFrame) {
  Run(kElementSubroutines);
  EXPECT_EQ(g_views.size(), 3U);
  EXPECT_TRUE(AFrameHoldsLocal("i1"));
}

constexpr const char* kResolvedNets =
    "module top;\n"
    "  function automatic logic resolve(input logic drivers[]);\n"
    "    $frame;\n"
    "    return drivers.size() > 0 ? drivers[0] : 1'bz;\n"
    "  endfunction\n"
    "  nettype logic rnet with resolve;\n"
    "  rnet n;\n"
    "  rnet na[2];\n"
    "  assign n = 1'b1;\n"
    "  assign na[0] = 1'b0;\n"
    "endmodule\n";

TEST_F(FramesOfARun,
       DISABLED_AResolutionFunctionsActivationIsAFrameFromItsNet) {
  Run(kResolvedNets);
  bool from_net = false;
  for (const FrameView& view : g_views) {
    from_net = from_net || (view.found && view.origin_type == vpiNet &&
                            view.origin == "top.n");
  }
  EXPECT_TRUE(from_net);
}

TEST_F(FramesOfARun,
       DISABLED_AResolutionFunctionsActivationIsAFrameFromItsNetArray) {
  Run(kResolvedNets);
  bool from_array = false;
  for (const FrameView& view : g_views) {
    from_array = from_array || (view.found && view.origin_type == vpiNetArray &&
                                view.origin == "top.na");
  }
  EXPECT_TRUE(from_array);
}

TEST_F(FramesOfARun, DISABLED_ABlockDeclaringAutomaticsIsAFrameFromItsScope) {
  Run("module top;\n"
      "  initial begin : b automatic int x; $frame; end\n"
      "endmodule\n");
  const FrameView& view = OnlyView();
  ASSERT_TRUE(view.found);
  EXPECT_EQ(view.origin_type, vpiNamedBegin);
  EXPECT_EQ(view.origin, "top.b");
  EXPECT_EQ(view.automatics, std::vector<std::string>{"x"});
}

constexpr const char* kBlockInATask =
    "module top;\n"
    "  task automatic tk();\n"
    "    int x;\n"
    "    begin : blk int z; $frame; end\n"
    "  endtask\n"
    "  initial tk();\n"
    "endmodule\n";

TEST_F(FramesOfARun, DISABLED_ABlockInsideATaskIsAFrameOfItsOwn) {
  Run(kBlockInATask);
  const FrameView& view = OnlyView();
  ASSERT_TRUE(view.found);
  EXPECT_EQ(view.origin_type, vpiNamedBegin);
  EXPECT_EQ(view.origin, "top.tk.blk");
  EXPECT_EQ(view.automatics, std::vector<std::string>{"z"});
  EXPECT_EQ(view.parent_automatics, std::vector<std::string>{"x"});
}

TEST_F(FramesOfARun,
       DISABLED_AParentFramesStmtIsTheScopeThatActivatedTheChild) {
  Run(kBlockInATask);
  const FrameView& view = OnlyView();
  EXPECT_EQ(view.parent_stmt_type, vpiNamedBegin);
  EXPECT_EQ(view.parent_stmt, "top.tk.blk");
}

TEST_F(FramesOfARun, DISABLED_AParentFramesStmtIsTheStatementHoldingTheCall) {
  Run("module top; int r;\n"
      "  function automatic int inner(); $frame; return 1; endfunction\n"
      "  function automatic int outer(); return inner(); endfunction\n"
      "  initial r = outer();\n"
      "endmodule\n");
  const FrameView& view = OnlyView();
  EXPECT_EQ(view.origin_type, vpiFuncCall);
  EXPECT_EQ(view.origin, "inner");
  EXPECT_EQ(view.parent_stmt_type, vpiReturn);
}

TEST_F(FramesOfARun, DISABLED_AParentOfTheActiveFrameIsNotActive) {
  Run("module top;\n"
      "  task automatic inner(); $frame; endtask\n"
      "  task automatic outer(); inner(); endtask\n"
      "  initial outer();\n"
      "endmodule\n");
  const FrameView& view = OnlyView();
  EXPECT_EQ(view.active, 1);
  EXPECT_EQ(view.parent_active, 0);
}

TEST_F(FramesOfARun, AFunctionFramesAutomaticsAreItsLocals) {
  Run("module top; int r;\n"
      "  function automatic int f(); int a; event e; $frame; return a;\n"
      "  endfunction\n"
      "  initial r = f();\n"
      "endmodule\n");
  EXPECT_EQ(OnlyView().automatics, (std::vector<std::string>{"a", "e"}));
}

TEST_F(FramesOfARun, ANamedEventArrayIsAmongAFramesAutomatics) {
  Run("module top;\n"
      "  task automatic tk(); event ea[2]; int x; $frame; endtask\n"
      "  initial tk();\n"
      "endmodule\n");
  EXPECT_EQ(OnlyView().automatics, (std::vector<std::string>{"ea", "x"}));
}

TEST_F(FramesOfARun, AFrameDeclaringNoAutomaticsIteratesToNone) {
  Run("module top;\n"
      "  task automatic tk(); $frame; endtask\n"
      "  initial tk();\n"
      "endmodule\n");
  const FrameView& view = OnlyView();
  EXPECT_TRUE(view.found);
  EXPECT_TRUE(view.automatics.empty());
}

TEST_F(FramesOfARun, AThreadInsideNoSubroutineHasNoActiveFrame) {
  Run("module top;\n"
      "  task automatic tk(); $frame; endtask\n"
      "  initial begin tk(); $frame; end\n"
      "endmodule\n");
  ASSERT_EQ(g_views.size(), 2U);
  EXPECT_TRUE(g_views[0].found);
  EXPECT_FALSE(g_views[1].found);
}

TEST_F(FramesOfARun, AFramesLocalTakesNoValueChangeCallback) {
  Run("module top;\n"
      "  task automatic tk(); int x; $frame; endtask\n"
      "  initial tk();\n"
      "endmodule\n");
  EXPECT_EQ(OnlyView().watchable, std::vector<bool>{false});
}

TEST_F(FramesOfARun, ANestedBlocksVariableTakesNoValueChangeCallback) {
  g_watch_name = "top.tk.blk.z";
  Run(kBlockInATask);
  EXPECT_TRUE(OnlyView().named_found);
  EXPECT_FALSE(OnlyView().named_watchable);
}

TEST_F(FramesOfARun, AStaticVariableBesideAnAutomaticTakesACallback) {
  g_watch_name = "top.b.s";
  Run("module top;\n"
      "  initial begin : b static int s; automatic int x; $frame; end\n"
      "endmodule\n");
  EXPECT_TRUE(OnlyView().named_watchable);
}

TEST_F(FramesOfARun,
       DISABLED_ATaskLocalRefusesADelayedPutAndTakesAnUndelayedOne) {
  Run("module top;\n"
      "  task automatic tk(); int x; $putauto; endtask\n"
      "  initial tk();\n"
      "endmodule\n");
  ASSERT_TRUE(g_put.reached);
  EXPECT_EQ(g_put.delayed_error, vpiError);
  EXPECT_EQ(g_put.undelayed_error, 0);
  EXPECT_EQ(g_put.value, 9);
}

TEST_F(FramesOfARun, ABlocksAutomaticRefusesADelayedPutAndTakesAnUndelayedOne) {
  g_put_name = "top.b.x";
  Run("module top;\n"
      "  initial begin : b automatic int x; $putauto; end\n"
      "endmodule\n");
  ASSERT_TRUE(g_put.reached);
  EXPECT_EQ(g_put.delayed_error, vpiError);
  EXPECT_EQ(g_put.undelayed_error, 0);
  EXPECT_EQ(g_put.value, 9);
}

class DelayedPutsOnAnAutomatic : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  bool RefusedWith(int mode) {
    auto* var = sim_ctx_.CreateVariable("a", 32);
    var->value = MakeLogic4VecVal(arena_, 32, 0);
    vpi_ctx_.Attach(sim_ctx_);
    VpiHandle h = vpi_ctx_.HandleByName("a", nullptr);
    if (h == nullptr) return false;
    h->automatic = true;
    s_vpi_value val = {};
    val.format = kVpiIntVal;
    val.value.integer = 55;
    s_vpi_time time = {};
    time.low = 10;
    vpi_ctx_.PutValue(h, &val, &time, mode);
    return var->value.ToUint64() == 0 &&
           vpi_ctx_.LastError().level == kVpiError;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(DelayedPutsOnAnAutomatic, ATransportDelayedPutIsRefused) {
  EXPECT_TRUE(RefusedWith(vpiTransportDelay));
}

TEST_F(DelayedPutsOnAnAutomatic, APureTransportDelayedPutIsRefused) {
  EXPECT_TRUE(RefusedWith(vpiPureTransportDelay));
}

}  // namespace
}  // namespace delta
