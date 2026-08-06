#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.2.2 Handle release. vpi_release_handle() causes a tool to release a
// handle; the underlying object is left in place, so a handle another VPI
// program has not released keeps referring to that object. Certain simulation
// events also release handles automatically: a restart releases all handles
// except the restart-callback handles; freeing a frame/thread's objects
// releases handles to those objects and their subelements; reclaiming a class
// object's memory releases handles to the object and its automatic data
// members. These tests observe the simulator applying those rules.
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

// §37.2.2: vpi_release_handle() releases a handle - afterward the handle is no
// longer a live handle to its object.
TEST_F(VpiHandleReleaseSim, ReleasingHandleMarksItReleased) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_FALSE(vpi_ctx_.HandleReleased(mod));
  vpi_ctx_.ReleaseHandle(mod);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
}

// §37.2.2: if a tool shares resources, one VPI program releasing a handle shall
// leave other programs able to refer to objects through handles they have not
// released. Releasing one handle to an object therefore leaves a distinct
// handle to the same object live and still referring to that object.
TEST_F(VpiHandleReleaseSim, ReleasingOneHandleLeavesDistinctHandleUsable) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);  // a second, distinct handle
  ASSERT_NE(other, mod);

  vpi_ctx_.ReleaseHandle(mod);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(other));
  // The distinct handle still refers to the same object.
  EXPECT_EQ(vpi_compare_objects(other, mod), 1);
}

// §37.2.2: a null handle names nothing to release, and releasing a handle more
// than once is harmless (it stays released).
TEST_F(VpiHandleReleaseSim, ReleasingNullIsHarmlessAndReleaseIsIdempotent) {
  vpi_ctx_.ReleaseHandle(nullptr);  // must not crash
  EXPECT_FALSE(vpi_ctx_.HandleReleased(nullptr));

  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.ReleaseHandle(mod);
  vpi_ctx_.ReleaseHandle(mod);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
}

// §37.2.2 (restart, list item 1): a simulation restart shall release all
// handles except the handles to cbStartOfRestart and cbEndOfRestart callbacks.
// Driving the real restart path (DispatchRestart) shows the two
// restart-callback handles surviving while an ordinary callback handle and an
// ordinary object handle are released.
TEST_F(VpiHandleReleaseSim, RestartReleasesAllButRestartCallbackHandles) {
  VpiCbData start{};
  start.reason = cbStartOfRestart;
  auto* start_cb = vpi_ctx_.RegisterCb(&start);

  VpiCbData end{};
  end.reason = cbEndOfRestart;
  auto* end_cb = vpi_ctx_.RegisterCb(&end);

  VpiCbData ordinary{};
  ordinary.reason = cbValueChange;  // obj left null - not a restart reason
  auto* ordinary_cb = vpi_ctx_.RegisterCb(&ordinary);

  auto* mod = vpi_ctx_.CreateModule("top", "top");

  vpi_ctx_.DispatchRestart();

  // The restart-callback handles survive.
  EXPECT_FALSE(vpi_ctx_.HandleReleased(start_cb));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(end_cb));
  // Every other handle is released.
  EXPECT_TRUE(vpi_ctx_.HandleReleased(ordinary_cb));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(mod));
}

// §37.2.2 (frame/thread free, list item 2): when the simulator frees objects
// belonging to a frame or thread, it shall release all handles to those objects
// and to any subelement of them, and the handles to callbacks placed on them.
TEST_F(VpiHandleReleaseSim, FreeingFrameObjectReleasesSubelementsAndCallbacks) {
  auto* frame_obj = vpi_ctx_.CreateModule("f", "f");
  auto* subelement = vpi_ctx_.CreateModule("f.s", "f.s");
  frame_obj->children.push_back(subelement);

  VpiCbData cb_data{};
  cb_data.reason = cbValueChange;
  cb_data.obj = subelement;  // a callback placed on the subelement
  auto* cb = vpi_ctx_.RegisterCb(&cb_data);

  vpi_ctx_.ReleaseFrameOrThreadObject(frame_obj);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(frame_obj));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(subelement));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(cb));
}

// §37.2.2 (class reclaim, list item 3): reclaiming a class object's memory
// shall release the handle to the class object, to any automatic data member,
// and to any subelement of those automatic members, plus callbacks placed on
// them. Static data members persist (NOTE 3) and their handles are not
// released.
TEST_F(VpiHandleReleaseSim, ReclaimingClassObjectReleasesAutomaticNotStatic) {
  auto* class_obj = vpi_ctx_.CreateModule("obj", "obj");

  auto* automatic_member = vpi_ctx_.CreateModule("obj.a", "obj.a");
  automatic_member->automatic = true;
  auto* automatic_subelement = vpi_ctx_.CreateModule("obj.a.s", "obj.a.s");
  automatic_member->children.push_back(automatic_subelement);

  auto* static_member = vpi_ctx_.CreateModule("obj.st", "obj.st");
  static_member->automatic = false;

  class_obj->children.push_back(automatic_member);
  class_obj->children.push_back(static_member);

  VpiCbData cb_data{};
  cb_data.reason = cbStmt;  // a callback placed on the automatic member
  cb_data.obj = automatic_member;
  auto* cb = vpi_ctx_.RegisterCb(&cb_data);

  vpi_ctx_.ReleaseClassObject(class_obj);

  EXPECT_TRUE(vpi_ctx_.HandleReleased(class_obj));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(automatic_member));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(automatic_subelement));
  EXPECT_TRUE(vpi_ctx_.HandleReleased(cb));
  // A static data member is not reclaimed with the class object.
  EXPECT_FALSE(vpi_ctx_.HandleReleased(static_member));
}

}  // namespace
}  // namespace delta
