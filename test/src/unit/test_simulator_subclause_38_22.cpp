#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiHandleMultiSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // An object of the requested kind, linked from both references. CreateModule
  // allocates a context-owned VpiObject; the test then stamps the category it
  // wants, the way the §37.37 delay tests build their handles.
  VpiHandle SharedObject(int type, VpiHandle ref1, VpiHandle ref2) {
    VpiHandle obj = vpi_ctx_.CreateModule("shared", "shared");
    obj->type = type;
    ref1->children.push_back(obj);
    ref2->children.push_back(obj);
    return obj;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.22 Returns: "vpiHandle -- Handle to an object." The one object of a
// many-to-one relationship is what comes back, not a container the application
// has to open: the Related routines row leaves the one-to-many traversal to
// vpi_iterate() and vpi_scan().
TEST_F(VpiHandleMultiSim, ReturnsTheObjectBothReferencesReach) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  VpiHandle path = SharedObject(vpiInterModPath, out_port, in_port);

  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, out_port, in_port), path);
}

// §38.22: the handle names the object itself, so what an application does to
// the handle it does to the object. Delays written through the returned handle
// are the delays the path holds.
TEST_F(VpiHandleMultiSim, TheReturnedHandleIsTheObjectItself) {
  auto* mod = vpi_ctx_.CreateModule("d", "d");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  VpiHandle path = SharedObject(vpiInterModPath, out_port, in_port);

  vpiHandle h = vpi_handle_multi(vpiInterModPath, out_port, in_port);
  ASSERT_NE(h, nullptr);

  s_vpi_time in[2] = {};
  in[0].real = 4.0;
  in[1].real = 6.0;
  s_vpi_delay put = {};
  put.da = in;
  put.no_of_delays = 2;
  put.time_type = vpiScaledRealTime;
  vpi_put_delays(h, &put);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(path, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 4.0);
  EXPECT_DOUBLE_EQ(out[1].real, 6.0);
}

// §38.22 Synopsis: "Obtain a handle for an object in a many-to-one
// relationship." An object only one of the references reaches stands in a
// relationship with that one alone, so it is not what this routine answers
// with.
TEST_F(VpiHandleMultiSim, NoHandleForAnObjectOnlyOneReferenceReaches) {
  auto* mod1 = vpi_ctx_.CreateModule("m1", "m1");
  vpi_ctx_.CreatePort("p1", kVpiInput, mod1);

  auto* mod2 = vpi_ctx_.CreateModule("m2", "m2");
  vpi_ctx_.CreatePort("p2", kVpiOutput, mod2);

  EXPECT_EQ(vpi_handle_multi(vpiPort, mod1, mod2), nullptr);
}

// §38.22 Arguments: the routine is given handles to reference objects. A
// relationship needs both of its ends, so a missing reference names none.
TEST_F(VpiHandleMultiSim, HandleMultiBothNullReturnsNull) {
  vpiHandle h = vpi_handle_multi(vpiPort, nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

// §38.22: one reference standing on its own is not a many-to-one relationship
// either, whatever the object it reaches.
TEST_F(VpiHandleMultiSim, HandleMultiOneNullReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("solo", "solo");
  vpi_ctx_.CreatePort("p", kVpiInput, mod);

  EXPECT_EQ(vpi_handle_multi(vpiPort, mod, nullptr), nullptr);
}

// §38.22: for a vpiInterModPath request the two reference objects are the
// output and input ports the path runs between, and they shall be of the same
// size. A pair whose widths differ cannot name a valid intermodule path, so the
// routine reports an error (§38.2) and returns no handle.
TEST_F(VpiHandleMultiSim, InterModPathRejectsDifferentlySizedPorts) {
  auto* mod = vpi_ctx_.CreateModule("top2", "top2");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  out_port->size = 8;
  in_port->size = 4;
  SharedObject(vpiInterModPath, out_port, in_port);

  vpiHandle h = vpi_handle_multi(vpiInterModPath, out_port, in_port);
  EXPECT_EQ(h, nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.22: the same-size requirement is the sentence about ports of an
// intermodule path. For any other object type the routine answers without
// inspecting the references' sizes, so a size mismatch must not turn into an
// error here.
TEST_F(VpiHandleMultiSim, SizeMismatchIgnoredForNonInterModPathType) {
  auto* mod1 = vpi_ctx_.CreateModule("u1", "u1");
  mod1->size = 8;
  auto* mod2 = vpi_ctx_.CreateModule("u2", "u2");
  mod2->size = 4;
  VpiHandle shared = SharedObject(vpiPort, mod1, mod2);

  EXPECT_EQ(vpi_handle_multi(vpiPort, mod1, mod2), shared);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.22: ports of the same size are accepted even when they sit at different
// levels of the hierarchy, which the subclause leaves unconstrained. The path
// linked from both ports is reached and no error is raised.
TEST_F(VpiHandleMultiSim, InterModPathAcceptsSameSizedPortsAcrossHierarchy) {
  auto* mod_a = vpi_ctx_.CreateModule("a", "top.a");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod_a);
  auto* mod_b = vpi_ctx_.CreateModule("b", "top.a.b");
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod_b);
  out_port->size = 16;
  in_port->size = 16;
  VpiHandle path = SharedObject(vpiInterModPath, out_port, in_port);

  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, out_port, in_port), path);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.22: the object answered for is of the type the request named. A reference
// pair sharing an object of some other kind has none of the kind asked for.
TEST_F(VpiHandleMultiSim, NoHandleWhenTheSharedObjectIsOfAnotherType) {
  auto* mod = vpi_ctx_.CreateModule("t", "t");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  SharedObject(vpiPort, out_port, in_port);

  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, out_port, in_port), nullptr);
}

}  // namespace
}  // namespace delta
