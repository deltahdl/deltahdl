#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3 -- VPI object classifications. "VPI objects are classified using data
// model diagrams. These diagrams provide a graphical representation of those
// objects within a SystemVerilog design to which the VPI routines shall provide
// access. The diagrams shall show the relationships between objects and the
// properties of each object."
//
// The clause reads one for the reader: "As an example, the simplified diagram
// in Figure 37-1 shows that there is a one-to-many relationship from objects of
// type module to objects of type net and a one-to-one relationship from objects
// of type net to objects of type module. Objects of type net have properties
// vpiName, vpiVector, and vpiSize with data types string, Boolean, and integer,
// respectively."
//
// That is two relations and three properties, stated of a design rather than of
// a diagram, and the cases below ask a design for all five. What makes them
// §37.3's rather than §37.16's is that the clause is what says a diagram is a
// claim about "those objects within a SystemVerilog design to which the VPI
// routines shall provide access": a relation drawn and not reachable, or a
// property named and not answered, is the diagram failing to classify anything.

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it, and §38.11 has vpi_get_str hand back one
// buffer every call reuses, so a name is copied as it is read.
int g_nets_from_module = 0;
int g_nets_reaching_back = 0;
std::string g_bus_name;
int g_bus_size = 0;
int g_bus_vector = -1;
int g_scalar_vector = -1;

int Figure37_1Calltf(const char*) {
  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
  if (mod == nullptr) return 0;

  // The one-to-many relation, which §38.23 walks with an iterator.
  vpiHandle nets = vpi_iterate(vpiNet, mod);
  if (nets == nullptr) return 0;
  for (vpiHandle net = vpi_scan(nets); net != nullptr; net = vpi_scan(nets)) {
    ++g_nets_from_module;

    // The one-to-one relation back, which §38.18 takes with a handle. It is the
    // module the walk started from and not merely a module.
    if (vpi_compare_objects(vpi_handle(vpiModule, net), mod) == 1) {
      ++g_nets_reaching_back;
    }

    // The three properties, read off whichever net this is.
    const char* name = vpi_get_str(vpiName, net);
    int size = vpi_get(vpiSize, net);
    int vector = vpi_get(vpiVector, net);
    if (name != nullptr && std::string(name) == "bus") {
      g_bus_name = name;
      g_bus_size = size;
      g_bus_vector = vector;
    } else {
      g_scalar_vector = vector;
    }
  }
  return 0;
}

void RegisterFigureProbe() {
  g_nets_from_module = 0;
  g_nets_reaching_back = 0;
  g_bus_name.clear();
  g_bus_size = 0;
  g_bus_vector = -1;
  g_scalar_vector = -1;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &Figure37_1Calltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// Figure 37-1's design: a module holding nets, instantiated so the application
// has a module object to start from. One net is a vector and one is not, which
// is what makes the Boolean property say something.
void RunFigure37_1(SimFixture& f) {
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

class VpiObjectClassifications : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiObjectClassifications, BothRelationsOfTheFigureAreTraversable) {
  RegisterFigureProbe();

  SimFixture f;
  RunFigure37_1(f);

  // The one-to-many: both nets the module declares.
  EXPECT_EQ(g_nets_from_module, 2);
  // The one-to-one, from each of them: the module they came from, compared as
  // §37.2.3 requires rather than by a C pointer equality the clause says
  // cannot settle it.
  EXPECT_EQ(g_nets_reaching_back, 2);
}

TEST_F(VpiObjectClassifications, TheThreePropertiesOfANetAreAnswered) {
  RegisterFigureProbe();

  SimFixture f;
  RunFigure37_1(f);

  // vpiName, a string: the name the source declared.
  EXPECT_EQ(g_bus_name, "bus");
  // vpiSize, an integer: the eight bits it was declared with.
  EXPECT_EQ(g_bus_size, 8);
  // vpiVector, a Boolean: true of the vector net and false of the scalar one,
  // which is the whole of what a Boolean property is worth. A net answered 0
  // to this whatever it was declared as before now, the property applying to a
  // port and to nothing else.
  EXPECT_EQ(g_bus_vector, 1);
  EXPECT_EQ(g_scalar_vector, 0);
}

}  // namespace
}  // namespace delta
