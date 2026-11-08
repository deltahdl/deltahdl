#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfacePortConnectionRulesElaboration,
     GenericInterfacePortConnectedToInterfaceInstance) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(interface port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     GenericInterfacePortConnectedToDistinctInterfaceType) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "interface other_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(interface port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  other_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortConnectedToHigherLevelInterfacePort) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(interface port_a);\n"
             "endmodule\n"
             "module mid(interface port_b);\n"
             "  child u(.port_a(port_b));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortConnectedToNetErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.port_a(w));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interface port 'port_a' must be connected to an interface instance or "
      "interface port",
      8, "23.3.3.4"));
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortConnectedToExpressionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u(.port_a(x + 1));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interface port 'port_a' must be connected to an interface instance or "
      "interface port",
      8, "23.3.3.4"));
}

TEST(InterfacePortConnectionRulesElaboration, UnconnectedInterfacePortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface port 'port_a' of module 'child' cannot "
                            "be left unconnected",
                            7, "23.3.3.4"));
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortConnectedToSameType) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(bus_if port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortConnectedToDifferentTypeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "interface other_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(bus_if port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  other_if inst();\n"
      "  child u(.port_a(inst));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface port 'port_a' requires interface type "
                            "'bus_if' but is connected to instance of type "
                            "'other_if'",
                            11, "23.3.3.4"));
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortConnectedByPositionToSameType) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(bus_if port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(inst);\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortConnectedByPositionToDifferentTypeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "interface other_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(bus_if port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  other_if inst();\n"
      "  child u(inst);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface port 'port_a' requires interface type "
                            "'bus_if' but is connected to instance of type "
                            "'other_if'",
                            11, "23.3.3.4"));
}

}  // namespace
