#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §36.10 -- VPI access to SystemVerilog objects and simulation objects. The VPI
// routines reach the objects of an instantiated design, one in which every
// instance of an object can be reached on its own: a module m holding a wire w
// and instantiated as m1 and m2 gives two separate objects m1.w and m2.w, each
// with related objects and properties of its own.
//
// The design below is the clause's own: one module holding a wire, instantiated
// twice. What the cases ask of it is what the sentence says -- that the two
// instances are reached separately and are not one object between them.

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it, and a handle is only good while the run
// holds it, so what a case reads back is what the application made of one.
bool g_m1_found = false;
bool g_m2_found = false;
bool g_wire_found = false;
int g_same_object = -1;
int g_wire_type = 0;
uint64_t g_m1_value = 0;
uint64_t g_m2_value = 0;

PLI_INT32 InspectCalltf(PLI_BYTE8*) {
  vpiHandle m1_r = vpi_handle_by_name(VpiText("m1.r"), nullptr);
  vpiHandle m2_r = vpi_handle_by_name(VpiText("m2.r"), nullptr);
  g_m1_found = m1_r != nullptr;
  g_m2_found = m2_r != nullptr;

  vpiHandle m1_w = vpi_handle_by_name(VpiText("m1.w"), nullptr);
  g_wire_found = m1_w != nullptr;
  if (m1_w != nullptr) g_wire_type = vpi_get(vpiType, m1_w);

  if (m1_r == nullptr || m2_r == nullptr) return 0;
  g_same_object = vpi_compare_objects(m1_r, m2_r);

  // Each instance carries its own storage, so a write through one is not a
  // write through the other.
  s_vpi_value put = {};
  put.format = vpiIntVal;
  put.value.integer = 42;
  vpi_put_value(m1_r, &put, nullptr, vpiNoDelay);

  s_vpi_value got = {};
  got.format = vpiIntVal;
  vpi_get_value(m1_r, &got);
  g_m1_value = static_cast<uint64_t>(got.value.integer);
  vpi_get_value(m2_r, &got);
  g_m2_value = static_cast<uint64_t>(got.value.integer);
  return 0;
}

// §36.6 attaches the design where the run holds a PLI application, so the
// registration is what puts the objects below within reach at all.
void RegisterProbe() {
  g_m1_found = false;
  g_m2_found = false;
  g_wire_found = false;
  g_same_object = -1;
  g_wire_type = 0;
  g_m1_value = 0;
  g_m2_value = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &InspectCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// The clause's design: a module holding a wire and a variable, instantiated
// twice, and a call that lets the application look at both instances.
void RunTwoInstances(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  int r;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  m m2();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class InstantiatedDesignAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.10: every instance of an object can be reached on its own, so the object
// inside m1 is reached under m1's name and the one inside m2 under m2's, and
// the two names do not lead to one object. The design was reachable only by a
// name with no instance in it before this: an object was entered under the one
// flat string the simulator keys it on, while §38.21 resolves a name a
// component at a time, so `m1.r` was split into two components and matched
// nothing.
TEST_F(InstantiatedDesignAccess, EachInstanceIsReachedUnderItsOwnName) {
  RegisterProbe();

  SimFixture f;
  RunTwoInstances(f);

  EXPECT_TRUE(g_m1_found);
  EXPECT_TRUE(g_m2_found);
  // §38.3: 1 when the two handles refer to the same underlying object. These
  // are two separate objects, so 0 is the answer the clause asks for.
  EXPECT_EQ(g_same_object, 0);
}

// §36.10: each of the two has related objects and properties of its own, so
// what one instance holds is not what the other holds. A write through m1's
// object lands in m1's storage and leaves m2's where it was -- which is also
// what says the two handles are not one object reached twice.
TEST_F(InstantiatedDesignAccess, EachInstanceCarriesItsOwnValue) {
  RegisterProbe();

  SimFixture f;
  RunTwoInstances(f);

  ASSERT_TRUE(g_m1_found);
  ASSERT_TRUE(g_m2_found);
  EXPECT_EQ(g_m1_value, 42u);
  EXPECT_EQ(g_m2_value, 0u);
}

// §36.10: the object the clause's own example names is a wire, and the run's
// nets were not put within reach of the applications at all -- only its
// variables were -- so `m1.w` named nothing whatever the shape of the name.
TEST_F(InstantiatedDesignAccess, TheClausesOwnExampleObjectIsAWire) {
  RegisterProbe();

  SimFixture f;
  RunTwoInstances(f);

  EXPECT_TRUE(g_wire_found);
  EXPECT_EQ(g_wire_type, vpiNet);
}

// §36.10 with §27.4: a generate block path names a block instance below the
// instance only while each step finds one; past a step that finds none it
// names nothing.
TEST(DesignWalk, AGenerateBlockPathStopsAtAStepThatFindsNothing) {
  VpiObject instance;
  instance.type = vpiModule;
  const HierPath kPath = {HierStep{"g"}, HierStep{"h"}};
  EXPECT_EQ(VpiGenScopeOf(&instance, kPath), nullptr);
}

// §36.10: attaching a design visits each instance the run built an object
// for. A design with no top, or whose first top stands for no module, has none
// to visit. An instance that stands for no module is passed over rather than
// followed, and a declaration the run built no object for is passed over too.
// A top written with a dot is walked whether it is the first top or a later
// one keyed under its own name.
TEST(DesignWalk, AttachPassesOverInstancesWithNothingToVisit) {
  for (int which = 0; which < 4; ++which) {
    VpiContext vpi_ctx;
    SetGlobalVpiContext(&vpi_ctx);
    SimFixture f;
    RtlirModule unnamed;
    unnamed.children.resize(1);
    RtlirModule dotted;
    dotted.name = "x.y";
    dotted.variables.resize(1);
    dotted.variables.front().name = "unbuilt";
    RtlirDesign design;
    if (which == 1) design.top_modules = {nullptr};
    if (which == 2) design.top_modules = {&unnamed, &dotted};
    if (which == 3) design.top_modules = {&dotted};
    vpi_ctx.Attach(f.ctx, &design);
    if (which < 2) EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
    SetGlobalVpiContext(nullptr);
  }
}

}  // namespace
}  // namespace delta
