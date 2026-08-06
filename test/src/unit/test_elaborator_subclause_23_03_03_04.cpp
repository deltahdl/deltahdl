
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §23.3.3.4: a generic interface port (declared with the `interface` keyword,
// hence no named interface type) may be connected to an interface instance of
// any type. This also covers the baseline rule that an interface port shall be
// connected to an interface instance.
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

// §23.3.3.4: "any type" for a generic interface port is genuine, not an
// accidental match. A generic port accepts an instance of `other_if` even
// though a named `bus_if` port rejects that exact type (see
// NamedInterfacePortConnectedToDifferentTypeErrors), witnessing that the
// generic port carries no required type to check against.
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

// §23.3.3.4: an interface port may be connected to a higher-level interface
// port (distinct production path from connecting to a local instance).
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

// §23.3.3.4: the connection target must be an interface instance or interface
// port. An identifier naming an ordinary net is neither, so it is illegal.
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
  EXPECT_TRUE(f.has_errors);
}

// §23.3.3.4: a non-identifier expression can never name an interface instance
// or port, so connecting one to an interface port is illegal.
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
  EXPECT_TRUE(f.has_errors);
}

// §23.3.3.4: an interface port cannot be left unconnected.
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
  EXPECT_TRUE(f.has_errors);
}

// §23.3.3.4: a named interface type port may be connected to an interface
// instance of the identical type.
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

// §23.3.3.4: a named interface type port shall be connected to an interface
// instance of the identical type; a different interface type is illegal.
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
  EXPECT_TRUE(f.has_errors);
}

// §23.3.3.4: the interface-port connection rules apply regardless of the
// connection syntax used to deliver the interface. A named interface-type port
// connected by positional (ordered) list to an instance of the identical type
// is legal, reaching the rule through the ordered-binding path rather than a
// named `.port_a(...)` connection.
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

// §23.3.3.4: the identical-type requirement for a named interface-type port is
// enforced even when the interface is delivered by a positional connection; a
// positionally connected instance of a different interface type is rejected.
// This witnesses that the type check fires on ordered bindings, not only named
// ones.
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
