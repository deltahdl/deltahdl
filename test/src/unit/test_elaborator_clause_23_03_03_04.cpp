
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

// TEMP PROBE: dump runtime port state for the DifferentType scenario so CI logs
// reveal which guard suppresses the §23.3.3.4 check. Remove after diagnosis.
TEST(InterfacePortConnectionRulesElaboration, ZzzProbeDifferentType) {
  ElabFixture f;
  auto* d = ElaborateSrc(
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
  ADD_FAILURE() << "PROBE has_errors=" << f.has_errors
                << " design=" << (d != nullptr);
  if (!d) return;
  auto it = d->all_modules.find("top");
  ADD_FAILURE() << "PROBE top_found=" << (it != d->all_modules.end())
                << " nmodules=" << d->all_modules.size();
  if (it == d->all_modules.end()) return;
  auto* top = it->second;
  ADD_FAILURE() << "PROBE top_children=" << top->children.size();
  for (const auto& ch : top->children) {
    ADD_FAILURE() << "PROBE child inst_name=" << ch.inst_name
                  << " module_name=" << ch.module_name
                  << " resolved=" << (ch.resolved != nullptr)
                  << " nbindings=" << ch.port_bindings.size();
    if (ch.resolved) {
      for (const auto& p : ch.resolved->ports) {
        ADD_FAILURE() << "PROBE   port name=" << p.name
                      << " is_ifc=" << p.is_interface_port
                      << " ifc_type=" << p.interface_type_name;
      }
    }
    for (const auto& b : ch.port_bindings) {
      ADD_FAILURE() << "PROBE   binding port=" << b.port_name
                    << " conn=" << (b.connection != nullptr) << " kind="
                    << (b.connection ? static_cast<int>(b.connection->kind)
                                     : -1)
                    << " text="
                    << (b.connection ? b.connection->text : std::string_view{});
    }
  }
}

}  // namespace
