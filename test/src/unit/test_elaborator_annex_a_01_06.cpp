#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// A.1.6: an interface's items, interface_or_generate_item, reach the module
// common items and the extern task and function prototypes, but never the
// udp_instantiation only A.1.4's module_or_generate_item reaches. A UDP
// instance reads as a module instance until its name resolves, so it is the
// elaborator that reports one standing among an interface's items (#7522).
TEST(InterfaceOrGenerateItem, AUdpInstanceIsNoInterfaceItem) {
  ElabFixture f;
  ElaborateSrc(
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "interface ifc;\n"
      "  wire a, z;\n"
      "  inv u(z, a);\n"
      "endinterface\n"
      "module top; ifc i(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive cannot be instantiated inside "
                            "interface 'ifc'",
                            6, "A.1.6"));
}

// A.1.6: a generate block of an interface holds interface items too, so a UDP
// instance in one is no more an interface item than one among the
// interface's own items (#7522).
TEST(InterfaceOrGenerateItem, AUdpInstanceInAnInterfaceGenerateBlock) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  wire a, z;\n"
      "  if (1) begin : g\n"
      "    inv u(z, a);\n"
      "  end\n"
      "endinterface\n"
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; ifc i(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive cannot be instantiated inside "
                            "interface 'ifc'",
                            4, "A.1.6"));
}

// A.1.4: a module's items do reach udp_instantiation, so the same instance in
// a module is reported nowhere.
TEST(InterfaceOrGenerateItem, AUdpInstanceInAModuleIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  wire a, z;\n"
      "  inv u(z, a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
