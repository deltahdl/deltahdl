#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

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
