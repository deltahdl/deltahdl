#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceObjectAccessElaboration,
     HierarchicalAccessBypassesModportRestrictionFromContainingScope_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  integer I;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module sub(ebus_i.mp i);\n"
             "endmodule\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  sub s1(ebus.mp);\n"
             "  initial top.ebus.I = 0;\n"
             "endmodule\n"));
}

TEST(InterfaceObjectAccessElaboration,
     HierarchicalAccessFromInsideModportPortBypassesModport_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  integer I;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module sub(ebus_i.mp i);\n"
             "  initial top.ebus.I = 0;\n"
             "endmodule\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  sub s1(ebus.mp);\n"
             "endmodule\n"));
}

TEST(InterfaceObjectAccessElaboration, PortMemberReadOfSignalInModport_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module sub(ebus_i.mp i);\n"
             "  logic P;\n"
             "  assign P = i.Q;\n"
             "endmodule\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  sub s1(ebus.mp);\n"
             "endmodule\n"));
}

// §25.10 states that "A modport may be used to restrict access to objects
// declared in an interface that are referenced through a port connection or
// virtual interface by explicitly listing the accessible objects in the
// modport". The restriction is the modport's own, stated in §25.5: "To restrict
// interface access within a module, there are modport lists with directions
// declared within the interface." The elaborator reports the refused access
// under §25.5, and InterfaceModportAccess.UnlistedMemberNames25_5 in
// test/src/unit/test_elaborator_subclause_25_05.cpp reads the same report back
// and asserts that subclause.
TEST(InterfaceObjectAccessElaboration,
     PortMemberAccessToSignalNotListedInModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface ebus_i;\n"
      "  integer I;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  integer P;\n"
      "  initial P = i.I;\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'I' is not accessible through modport 'mp' of interface "
                    "'ebus_i'",
                    8, "25.5"));
}

TEST(InterfaceObjectAccessElaboration, PortMemberAccessToInterfaceTypedef_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  typedef enum {Y, N} choice;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module sub(ebus_i.mp i);\n"
             "  typedef i.choice yes_no;\n"
             "  yes_no P;\n"
             "endmodule\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  sub s1(ebus.mp);\n"
             "endmodule\n"));
}

TEST(InterfaceObjectAccessElaboration,
     PortMemberAccessToInterfaceLocalparam_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  localparam True = 1;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module sub(ebus_i.mp i);\n"
             "  integer P;\n"
             "  initial P = i.True;\n"
             "endmodule\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  sub s1(ebus.mp);\n"
             "endmodule\n"));
}

TEST(InterfaceObjectAccessElaboration, VifMemberAccessToSignalInModport_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  virtual ebus_i.mp v;\n"
             "  logic P;\n"
             "  initial begin\n"
             "    v = ebus;\n"
             "    P = v.Q;\n"
             "  end\n"
             "endmodule\n"));
}

// §25.10 names the virtual interface as the second way a reference is subject
// to the modport restriction, so the same refusal and the same §25.5 report
// follow when the interface is reached through a virtual interface rather than
// through a port connection.
TEST(InterfaceObjectAccessElaboration,
     VifMemberAccessToSignalNotListedInModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface ebus_i;\n"
      "  integer I;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  virtual ebus_i.mp v;\n"
      "  integer P;\n"
      "  initial begin\n"
      "    v = ebus;\n"
      "    P = v.I;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'I' is not accessible through modport 'mp' of interface "
                    "'ebus_i'",
                    12, "25.5"));
}

TEST(InterfaceObjectAccessElaboration,
     VifMemberAccessToInterfaceLocalparam_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  localparam True = 1;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  virtual ebus_i.mp v;\n"
             "  integer P;\n"
             "  initial begin\n"
             "    v = ebus;\n"
             "    P = v.True;\n"
             "  end\n"
             "endmodule\n"));
}

// Claim 3, operand kind `parameter`: a parameter is not modport-listable, so a
// modport-scoped port reference to it stays accessible, like the localparam and
// typedef cases but exercising the distinct parameter declaration kind.
TEST(InterfaceObjectAccessElaboration,
     PortMemberAccessToInterfaceParameter_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  parameter Width = 4;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module sub(ebus_i.mp i);\n"
             "  integer P;\n"
             "  initial P = i.Width;\n"
             "endmodule\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  sub s1(ebus.mp);\n"
             "endmodule\n"));
}

// Claim 3, continuous-assignment position: a non-listable object (localparam)
// reached through a modport port inside a continuous assignment stays
// accessible; this drives the elaborator's continuous-assignment walk arm
// rather than the procedural-statement walk the other Claim 3 tests use.
TEST(InterfaceObjectAccessElaboration,
     PortMemberAccessToLocalparamInContinuousAssign_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  localparam True = 1;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module sub(ebus_i.mp i);\n"
             "  logic P;\n"
             "  assign P = i.True;\n"
             "endmodule\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  sub s1(ebus.mp);\n"
             "endmodule\n"));
}

// Claim 1, virtual-interface-coexistence position: hierarchical access to a
// non-modport member stays available even when the same interface instance is
// also reached through a virtual interface, matching the "regardless of whether
// also accessed through a virtual interface" part of the rule.
TEST(InterfaceObjectAccessElaboration,
     HierarchicalAccessBypassesModportWhenAlsoAccessedViaVirtualInterface_Ok) {
  EXPECT_TRUE(
      ElabOk("interface ebus_i;\n"
             "  integer I;\n"
             "  logic Q;\n"
             "  modport mp(input Q);\n"
             "endinterface\n"
             "module top;\n"
             "  ebus_i ebus();\n"
             "  virtual ebus_i.mp v;\n"
             "  initial begin\n"
             "    v = ebus;\n"
             "    top.ebus.I = 0;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
