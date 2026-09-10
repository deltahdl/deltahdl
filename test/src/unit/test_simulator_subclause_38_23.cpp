#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiIterateSim : public ::testing::Test {
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

TEST_F(VpiIterateSim, IterateModuleChildPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

// §38.23: the iterator walks "all objects of type type associated with object
// ref", so the regs of a run are reached by asking the scope that holds them.
// §37.4.3 gives a NULL reference only to a relationship the diagrams draw from
// a circle, and a scope's regs are drawn from the scope.
TEST_F(VpiIterateSim, IterateRegsOfAScopeAfterAttach) {
  sim_ctx_.CreateVariable("m1.v1", 8);
  sim_ctx_.CreateVariable("m1.v2", 16);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
  ASSERT_NE(mod, nullptr);

  vpiHandle iter = vpi_iterate(vpiReg, mod);
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST_F(VpiIterateSim, ScanNullIteratorReturnsNull) {
  EXPECT_EQ(vpi_scan(nullptr), nullptr);
}

// §38.23: the returned handle is an iterator whose own type is vpiIterator,
// not the type of the objects being traversed.
TEST_F(VpiIterateSim, IteratorHandleTypeIsIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_get(vpiType, iter), vpiIterator);
}

// §38.23: vpi_handle(vpiUse, iterator) recovers the reference object the
// iterator was created over.
TEST_F(VpiIterateSim, HandleVpiUseReturnsReferenceObject) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_handle(vpiUse, iter), mod);
}

// §38.23: unless otherwise specified, iterating a protected object is an error,
// so no iterator handle is produced.
TEST_F(VpiIterateSim, IterateProtectedObjectReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  mod->is_protected = true;

  EXPECT_EQ(vpi_iterate(vpiPort, mod), nullptr);
}

// §38.23: when no objects of the requested type are associated with the
// reference handle, vpi_iterate() returns NULL.
TEST_F(VpiIterateSim, IterateNoMatchingObjectsReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  EXPECT_EQ(vpi_iterate(vpiParameter, mod), nullptr);
}

// -----------------------------------------------------------------------------
// §38.23's own worked example. The clause ends with an application that walks
// a module's nets -- "the following example application uses vpi_iterate() and
// vpi_scan() to display each net (including the size for vectors) declared in
// the module" -- built out of vpi_iterate(vpiNet, mod), vpi_scan, vpiName and
// vpiSize.
//
// Every case above hands vpi_iterate objects it made itself, which says what
// the routine does with an object and nothing about a design having one. These
// run the example against a design.
// -----------------------------------------------------------------------------

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it, and vpi_get_str hands back one buffer
// every call reuses (§38.11), so the names are copied as they are read.
int g_nets_seen = 0;
std::string g_first_net_name;
std::string g_second_net_name;
int g_widest_net_size = 0;

int DisplayNetsCalltf(const char*) {
  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiNet, mod);
  if (itr == nullptr) return 0;
  for (vpiHandle net = vpi_scan(itr); net != nullptr; net = vpi_scan(itr)) {
    ++g_nets_seen;
    const char* name = vpi_get_str(vpiName, net);
    if (name != nullptr) {
      (g_nets_seen == 1 ? g_first_net_name : g_second_net_name) = name;
    }
    int size = vpi_get(vpiSize, net);
    if (size > g_widest_net_size) g_widest_net_size = size;
  }
  return 0;
}

void RegisterNetProbe() {
  g_nets_seen = 0;
  g_first_net_name.clear();
  g_second_net_name.clear();
  g_widest_net_size = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &DisplayNetsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// A module declaring the example's two shapes of net -- a scalar and a vector
// -- instantiated so the application has a module handle to iterate from.
void RunAModuleOfTwoNets(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class VpiIterateInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiIterateInARun, TheIterationWalksEveryNetTheModuleDeclares) {
  RegisterNetProbe();

  SimFixture f;
  RunAModuleOfTwoNets(f);

  // §38.23: "vpi_iterate() shall be used to traverse one-to-many
  // relationships", and a module to its nets is one of them. Both of the
  // module's nets are walked, and each answers to the name the source gave it.
  EXPECT_EQ(g_nets_seen, 2);
  EXPECT_TRUE(g_first_net_name == "w" || g_second_net_name == "w");
  EXPECT_TRUE(g_first_net_name == "bus" || g_second_net_name == "bus");
}

TEST_F(VpiIterateInARun, TheExamplesVectorNetReportsItsSize) {
  RegisterNetProbe();

  SimFixture f;
  RunAModuleOfTwoNets(f);

  // The example displays "the size for vectors", read off each net the
  // iteration handed back. The wider of the two is the eight-bit bus, which is
  // a size only the net object the design built carries -- one made by hand
  // carries whatever the case put in it.
  EXPECT_EQ(g_widest_net_size, 8);
}

}  // namespace
}  // namespace delta
