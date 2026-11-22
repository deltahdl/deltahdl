#include <gtest/gtest.h>

#include <functional>
#include <string>
#include <vector>

#include "helpers_event_callbacks.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::function<void(p_cb_data)>& Inspector() {
  static std::function<void(p_cb_data)> inspector;
  return inspector;
}

PLI_INT32 Inspect(p_cb_data cb) {
  Inspector()(cb);
  return 0;
}

vpiHandle PlaceInspected(int reason, vpiHandle obj) {
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = &Inspect;
  data.obj = obj;
  return vpi_register_cb(&data);
}

std::vector<int>& Seen() {
  static std::vector<int> seen;
  return seen;
}

std::vector<vpiHandle>& Kept() {
  static std::vector<vpiHandle> kept;
  return kept;
}

int ValueOf(vpiHandle obj) {
  if (obj == nullptr) return -1000;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(obj, &value);
  return value.value.integer;
}

vpiHandle MemberNamed(int relation, vpiHandle in, const std::string& name) {
  vpiHandle it = in == nullptr ? nullptr : vpi_iterate(relation, in);
  while (vpiHandle member = it == nullptr ? nullptr : vpi_scan(it)) {
    const char* own = vpi_get_str(vpiName, member);
    if (own != nullptr && name == own) {
      vpi_release_handle(it);
      return member;
    }
  }
  return nullptr;
}

vpiHandle ClassTypespecOf(const char* var) {
  return vpi_handle(vpiTypespec, TopObject(var));
}

class LifetimeCallbacksOfARun : public EventCallbacksOfARun {
 protected:
  void SetUp() override {
    EventCallbacksOfARun::SetUp();
    Seen().clear();
    Kept().clear();
    Inspector() = [](p_cb_data) {};
  }

  void RunAndCollect(const std::string& src) {
    Run(src);
    f_.ctx.CollectGarbage();
  }

  bool Released(vpiHandle handle) const {
    return vpi_.HandleReleased(VpiObjectOf(handle));
  }
};

TEST_F(LifetimeCallbacksOfARun, ACreateObjRoutineSeesTheConstructorsValue) {
  Armer() = [] { PlaceInspected(cbCreateObj, ClassTypespecOf("top.c")); };
  Inspector() = [](p_cb_data cb) {
    Seen().push_back(ValueOf(MemberNamed(vpiVariables, cb->obj, "x")));
  };
  Run("module top;\n"
      "  class C; int x; function new; x = 5; endfunction endclass C c;\n"
      "  initial begin $arm; c = new; end\n"
      "endmodule\n");
  EXPECT_EQ(Seen(), (std::vector<int>{5}));
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AShallowCopyInAnAssignmentCallsCreateObj) {
  Armer() = [] { PlaceInspected(cbCreateObj, ClassTypespecOf("top.c1")); };
  Inspector() = [](p_cb_data cb) {
    Seen().push_back(ValueOf(MemberNamed(vpiVariables, cb->obj, "x")));
  };
  Run("module top; class C; int x; endclass C c1; C c2;\n"
      "  initial begin $arm; c1 = new; c1.x = 4; c2 = new c1; end\n"
      "endmodule\n");
  EXPECT_EQ(Seen(), (std::vector<int>{0, 4}));
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AShallowCopyInADeclarationCallsCreateObj) {
  Armer() = [] { PlaceInspected(cbCreateObj, ClassTypespecOf("top.c1")); };
  Inspector() = [](p_cb_data cb) {
    Seen().push_back(ValueOf(MemberNamed(vpiVariables, cb->obj, "x")));
  };
  Run("module top; class C; int x; endclass C c1;\n"
      "  initial begin $arm; c1 = new; c1.x = 6;\n"
      "    begin automatic C c2 = new c1; end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(Seen(), (std::vector<int>{0, 6}));
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AShallowCopyInAPropertyInitializerCallsIt) {
  Armer() = [] { PlaceInspected(cbCreateObj, ClassTypespecOf("top.c1")); };
  Inspector() = [](p_cb_data cb) {
    Seen().push_back(ValueOf(MemberNamed(vpiVariables, cb->obj, "x")));
  };
  Run("module top; class C; int x = 3; endclass C c1;\n"
      "  class D; C first = new; C second = new first; endclass D d;\n"
      "  initial begin $arm; d = new; end\n"
      "endmodule\n");
  EXPECT_EQ(Seen(), (std::vector<int>{3, 3}));
}

constexpr const char* kFramedCalls =
    "module top; timeunit 1ns; timeprecision 1ns;\n"
    "  task automatic tk(input int n);\n"
    "    automatic logic [3:0] k = 7;\n"
    "    static int s = 2;\n"
    "    #n;\n"
    "  endtask\n"
    "  function automatic int fn(input int n);\n"
    "    automatic int k = 7;\n"
    "    return n;\n"
    "  endfunction\n"
    "  int r;\n"
    "  initial begin $arm; #1 tk(4); r = fn(9); end\n"
    "endmodule\n";

void NoteAutomatics(p_cb_data cb) {
  Seen().push_back(ValueOf(MemberNamed(vpiAutomatics, cb->obj, "k")));
  Seen().push_back(ValueOf(MemberNamed(vpiAutomatics, cb->obj, "n")));
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AStartOfFrameRoutineSeesInitializedAutomatics) {
  Armer() = [] { PlaceInspected(cbStartOfFrame, nullptr); };
  Inspector() = &NoteAutomatics;
  Run(kFramedCalls);
  EXPECT_EQ(Seen(), (std::vector<int>{7, 4, 7, 9}));
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AnEndOfFrameRoutineStillSeesItsAutomatics) {
  Armer() = [] { PlaceInspected(cbEndOfFrame, nullptr); };
  Inspector() = [](p_cb_data cb) {
    Seen().push_back(vpi_get(vpiType, cb->obj));
    NoteAutomatics(cb);
  };
  Run(kFramedCalls);
  EXPECT_EQ(Seen(), (std::vector<int>{vpiFrame, 7, 4, vpiFrame, 7, 9}));
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AnEndingFramesAutomaticIsReleasedAfterward) {
  Armer() = [] { PlaceInspected(cbEndOfFrame, nullptr); };
  Inspector() = [](p_cb_data cb) {
    if (!Kept().empty()) return;
    vpiHandle k = MemberNamed(vpiAutomatics, cb->obj, "k");
    Kept().push_back(k);
    Kept().push_back(vpi_handle_by_index(k, 0));
    Kept().push_back(PlaceEventCallback(cbValueChange, k));
  };
  Run(kFramedCalls);
  ASSERT_EQ(Kept().size(), 3u);
  for (vpiHandle handle : Kept()) {
    ASSERT_NE(handle, nullptr);
    EXPECT_TRUE(Released(handle));
  }
}

TEST_F(LifetimeCallbacksOfARun, AStaticLocalOutlivesItsTasksFrame) {
  Armer() = [] {
    vpiHandle s = TopObject("top.tk.s");
    Kept().push_back(s);
    Kept().push_back(PlaceEventCallback(cbValueChange, s));
  };
  Run(kFramedCalls);
  ASSERT_EQ(Kept().size(), 2u);
  for (vpiHandle handle : Kept()) {
    ASSERT_NE(handle, nullptr);
    EXPECT_FALSE(Released(handle));
  }
}

vpiHandle& FramesThread() {
  static vpiHandle thread = nullptr;
  return thread;
}

TEST_F(LifetimeCallbacksOfARun, AThreadEndsAfterTheFrameItActivated) {
  FramesThread() = nullptr;
  Armer() = [] {
    PlaceInspected(cbEndOfFrame, nullptr);
    PlaceInspected(cbEndOfThread, nullptr);
  };
  Inspector() = [](p_cb_data cb) {
    if (cb->reason == cbEndOfFrame) {
      FramesThread() = vpi_handle(vpiThread, cb->obj);
      Seen().push_back(cbEndOfFrame);
      return;
    }
    if (FramesThread() != nullptr &&
        vpi_compare_objects(FramesThread(), cb->obj) != 0) {
      Seen().push_back(cbEndOfThread);
    }
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  task automatic tk; #3; endtask\n"
      "  initial begin $arm; fork tk(); join end\n"
      "endmodule\n");
  EXPECT_EQ(Seen(), (std::vector<int>{cbEndOfFrame, cbEndOfThread}));
}

TEST_F(LifetimeCallbacksOfARun, AnEndOfThreadRoutineSeesAValidThread) {
  Armer() = [] { PlaceInspected(cbEndOfThread, nullptr); };
  Inspector() = [](p_cb_data cb) {
    Seen().push_back(vpi_get(vpiType, cb->obj));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  initial begin $arm; fork #2; join end\n"
      "endmodule\n");
  ASSERT_FALSE(Seen().empty());
  for (int type : Seen()) EXPECT_EQ(type, vpiThread);
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AnEndOfObjectCallbackOnAFrameIsAboutItAlone) {
  Armer() = [] { PlaceInspected(cbStartOfFrame, nullptr); };
  Inspector() = [](p_cb_data cb) {
    if (cb->reason == cbStartOfFrame) {
      if (Kept().empty())
        Kept().push_back(PlaceInspected(cbEndOfObject, cb->obj));
      return;
    }
    s_vpi_time now = {};
    now.type = vpiSimTime;
    vpi_get_time(nullptr, &now);
    Seen().push_back(static_cast<int>(now.low));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  task automatic tk(input int n); #n; endtask\n"
      "  initial begin $arm; tk(2); tk(5); end\n"
      "endmodule\n");
  ASSERT_EQ(Kept().size(), 1u);
  EXPECT_NE(Kept()[0], nullptr);
  EXPECT_EQ(Seen(), (std::vector<int>{2}));
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AnEndOfObjectCallbackOnAThreadIsAboutItAlone) {
  Armer() = [] { PlaceInspected(cbStartOfThread, nullptr); };
  Inspector() = [](p_cb_data cb) {
    if (cb->reason == cbStartOfThread) {
      if (Kept().empty())
        Kept().push_back(PlaceInspected(cbEndOfObject, cb->obj));
      return;
    }
    s_vpi_time now = {};
    now.type = vpiSimTime;
    vpi_get_time(nullptr, &now);
    Seen().push_back(static_cast<int>(now.low));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  initial begin $arm; fork #2; #5; join end\n"
      "endmodule\n");
  ASSERT_EQ(Kept().size(), 1u);
  EXPECT_NE(Kept()[0], nullptr);
  EXPECT_EQ(Seen(), (std::vector<int>{2}));
}

constexpr const char* kDroppedObject =
    "module top; class C; logic [3:0] x; static int s = 8; endclass C c;\n"
    "  initial begin $arm; c = new; c.x = 9; c = null; end\n"
    "endmodule\n";

TEST_F(LifetimeCallbacksOfARun, AReclaimRoutineReadsTheObjectsProperties) {
  Armer() = [] { PlaceInspected(cbReclaimObj, ClassTypespecOf("top.c")); };
  Inspector() = [](p_cb_data cb) {
    Seen().push_back(vpi_get(vpiType, cb->obj));
    Seen().push_back(vpi_get(vpiType, vpi_handle(vpiClassTypespec, cb->obj)));
    Seen().push_back(ValueOf(MemberNamed(vpiVariables, cb->obj, "x")));
  };
  RunAndCollect(kDroppedObject);
  EXPECT_EQ(Seen(), (std::vector<int>{vpiClassObj, vpiClassTypespec, 9}));
}

void KeepMembers(p_cb_data cb) {
  Kept().push_back(MemberNamed(vpiVariables, cb->obj, "x"));
  Kept().push_back(MemberNamed(vpiVariables, cb->obj, "s"));
}

void KeepPartsOfX(p_cb_data cb) {
  vpiHandle x = MemberNamed(vpiVariables, cb->obj, "x");
  Kept().push_back(vpi_handle_by_index(x, 0));
  Kept().push_back(PlaceEventCallback(cbValueChange, x));
}

TEST_F(LifetimeCallbacksOfARun, AReclaimedPropertyIsReleasedButAStaticIsNot) {
  Armer() = [] { PlaceInspected(cbReclaimObj, ClassTypespecOf("top.c")); };
  Inspector() = &KeepMembers;
  RunAndCollect(kDroppedObject);
  ASSERT_EQ(Kept().size(), 2u);
  ASSERT_NE(Kept()[0], nullptr);
  ASSERT_NE(Kept()[1], nullptr);
  EXPECT_TRUE(Released(Kept()[0]));
  EXPECT_FALSE(Released(Kept()[1]));
  EXPECT_EQ(ValueOf(Kept()[1]), 8);
}

TEST_F(LifetimeCallbacksOfARun,
       DISABLED_AReclaimedPropertysBitAndCallbackAreReleased) {
  Armer() = [] { PlaceInspected(cbReclaimObj, ClassTypespecOf("top.c")); };
  Inspector() = &KeepPartsOfX;
  RunAndCollect(kDroppedObject);
  ASSERT_EQ(Kept().size(), 2u);
  for (vpiHandle handle : Kept()) {
    ASSERT_NE(handle, nullptr);
    EXPECT_TRUE(Released(handle));
  }
}

}  // namespace
}  // namespace delta
