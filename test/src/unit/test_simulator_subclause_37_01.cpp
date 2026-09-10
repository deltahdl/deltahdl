#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.1 names what Clause 37 is for: "using VPI data models" and "VPI data
// model diagrams". Using one begins somewhere, and §37.5 detail 1 says where -
// "top-level modules shall be accessed using vpi_iterate() with a NULL
// reference object". An application walks down from there.
//
// A design had no such object to reach. The simulator keys an instance's
// objects on a flat name and a top module carries the empty prefix, so what the
// attach entered were the top's own contents under their bare names and the top
// itself was an object of no kind; the iteration that reaches the tops reached
// none of them, and VpiObject::top_module - read by that iteration's filter and
// by vpi_get(vpiTopModule) - was written by nothing. So the first step of using
// the data model against a design took an application nowhere.

// What the application found walking down from the top.
int g_tops_seen = 0;
std::string g_top_name;
int g_top_is_top = 0;
bool g_reached_instance = false;
bool g_reached_net = false;
int g_instance_is_top = 0;

int WalkFromTheTopCalltf(const char*) {
  vpiHandle tops = vpi_iterate(vpiModule, nullptr);
  if (tops == nullptr) return 0;
  vpiHandle top = nullptr;
  while (vpiHandle next = vpi_scan(tops)) {
    ++g_tops_seen;
    top = next;
  }
  if (top == nullptr) return 0;

  const char* name = vpi_get_str(vpiName, top);
  if (name != nullptr) g_top_name = name;
  g_top_is_top = vpi_get(vpiTopModule, top);

  // The diagrams' one-to-many traversal, from the top to what it holds.
  vpiHandle instances = vpi_iterate(vpiModule, top);
  if (instances != nullptr) {
    while (vpiHandle instance = vpi_scan(instances)) {
      g_reached_instance = true;
      g_instance_is_top = vpi_get(vpiTopModule, instance);
      vpiHandle nets = vpi_iterate(vpiNet, instance);
      if (nets == nullptr) continue;
      while (vpi_scan(nets) != nullptr) g_reached_net = true;
    }
  }
  return 0;
}

void RegisterWalkProbe() {
  g_tops_seen = 0;
  g_top_name.clear();
  g_top_is_top = 0;
  g_reached_instance = false;
  g_reached_net = false;
  g_instance_is_top = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &WalkFromTheTopCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class UsingTheDataModel : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §37.1 with §37.5 detail 1: an application reaches the design's one top module
// through the NULL-reference iteration, and the top says it is one.
TEST_F(UsingTheDataModel, AnApplicationReachesTheDesignsTopModule) {
  RegisterWalkProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_tops_seen, 1);
  EXPECT_EQ(g_top_name, "t");
  EXPECT_EQ(g_top_is_top, 1);
}

// §37.1: using the model is walking it. From the top the application reaches
// the instance the design elaborates and the net that instance declares, which
// is the one-to-many traversal §37.4.3 draws with a double arrow.
TEST_F(UsingTheDataModel, TheWalkGoesDownFromTheTop) {
  RegisterWalkProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_TRUE(g_reached_instance);
  EXPECT_TRUE(g_reached_net);
  // §37.5 detail 1: an instance below the top is a module too, and is not one
  // of the tops - which is what the NULL-reference iteration selects on.
  EXPECT_EQ(g_instance_is_top, 0);
}

}  // namespace
}  // namespace delta
