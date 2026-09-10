#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.4 (Key to data model diagrams): "This subclause contains the keys to the
// symbols used in the data model diagrams. Keys are provided for objects and
// classes, traversing relationships, and accessing properties."
//
// That is the claim of the subclause itself rather than of any one of its three
// children: the three keys together are what a data model diagram is read with,
// so a diagram of the standard read by all three answers. §37.3's Figure 37-1
// is the standard's own example of such a diagram, and what it draws is a
// one-to-many relationship from module to net, a one-to-one relationship back,
// and the properties vpiName, vpiFullName, vpiVector and vpiSize on the net.
//
// Read by the three keys:
//   - §37.4.1 (objects and classes): both enclosures are solid, so `module` and
//     `net` are objects and each is a kind an object reports as its vpiType.
//   - §37.4.3 (traversing relationships): the double arrow is walked with
//     vpi_iterate()/vpi_scan(), the single arrow with vpi_handle(), and neither
//     is tagged, so the type is the enclosure's word with "vpi" put in front.
//   - §37.4.2 (accessing properties): the integer and Boolean properties come
//     from vpi_get(), the string ones from vpi_get_str().
//
// The case runs that reading against a design, because a key is a key to the
// diagrams of a described design rather than to an object a test built.

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it.
std::string g_net_name;
std::string g_net_full_name;
std::string g_module_full_name;
int g_net_size = 0;
int g_net_vector = -1;
int g_net_type = 0;
int g_module_type = 0;
int g_nets_scanned = 0;
bool g_iteration_found_the_net = false;

int ReadFigureOneCalltf(const char*) {
  // §37.4.3: an untagged one-to-one relation drawn from `net` to `module` is
  // walked with vpi_handle() and the type is the enclosure's word.
  vpiHandle net = vpi_handle_by_name("t.m1.w", nullptr);
  if (net == nullptr) return 0;
  vpiHandle mod = vpi_handle(vpiModule, net);
  if (mod == nullptr) return 0;

  // §37.4.1: a solid enclosure holds an object, so each reports its own kind.
  g_net_type = vpi_get(vpiType, net);
  g_module_type = vpi_get(vpiType, mod);

  // §37.4.2: the Boolean and integer properties through vpi_get(), the string
  // ones through vpi_get_str().
  g_net_vector = vpi_get(vpiVector, net);
  g_net_size = vpi_get(vpiSize, net);
  if (const char* name = vpi_get_str(vpiName, net)) g_net_name = name;
  if (const char* full = vpi_get_str(vpiFullName, net)) g_net_full_name = full;
  if (const char* full = vpi_get_str(vpiFullName, mod)) {
    g_module_full_name = full;
  }

  // §37.4.3: the double arrow back from `module` to `net` is walked with
  // vpi_iterate() and vpi_scan(), and it reaches the net the single arrow came
  // from.
  vpiHandle itr = vpi_iterate(vpiNet, mod);
  if (itr == nullptr) return 0;
  while (vpiHandle scanned = vpi_scan(itr)) {
    ++g_nets_scanned;
    if (vpi_compare_objects(scanned, net) != 0) {
      g_iteration_found_the_net = true;
    }
  }
  return 0;
}

class VpiDataModelDiagramKeys : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_net_name.clear();
    g_net_full_name.clear();
    g_module_full_name.clear();
    g_net_size = 0;
    g_net_vector = -1;
    g_net_type = 0;
    g_module_type = 0;
    g_nets_scanned = 0;
    g_iteration_found_the_net = false;
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// The whole of §37.4's claim, on the diagram §37.3 draws: a design described in
// SystemVerilog answers every symbol of Figure 37-1 through the routine its key
// names. The vpiFullName of a net declared below a top module named only the
// part of the path below that top, so the string key read a name no application
// could pass back to vpi_handle_by_name().
TEST_F(VpiDataModelDiagramKeys, FigureOneIsReadByTheThreeKeys) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &ReadFigureOneCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  assign w = 8'h5a;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // §37.4.1: each solid enclosure is an object of the kind it names.
  EXPECT_EQ(g_net_type, vpiNet);
  EXPECT_EQ(g_module_type, vpiModule);

  // §37.4.2: "objects of type net have properties vpiName, vpiVector, and
  // vpiSize with data types string, Boolean, and integer, respectively", plus
  // the vpiFullName the figure draws beside vpiName.
  EXPECT_EQ(g_net_name, "w");
  EXPECT_EQ(g_net_full_name, "t.m1.w");
  EXPECT_EQ(g_net_size, 8);
  EXPECT_EQ(g_net_vector, 1);
  EXPECT_EQ(g_module_full_name, "t.m1");

  // §37.4.3: the double arrow reaches the net the single arrow was walked from.
  EXPECT_GT(g_nets_scanned, 0);
  EXPECT_TRUE(g_iteration_found_the_net);
}

}  // namespace
}  // namespace delta
