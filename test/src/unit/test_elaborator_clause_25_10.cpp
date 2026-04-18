#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceObjectAccessElaboration,
     HierarchicalReadOfSignalInInterfaceWithNoModports_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
      "  integer I;\n"
      "endinterface\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  integer sample;\n"
      "  initial sample = top.ebus.I;\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessElaboration,
     HierarchicalWriteOfSignalInInterfaceWithNoModports_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
      "  integer I;\n"
      "endinterface\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  initial top.ebus.I = 0;\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessElaboration,
     HierarchicalAccessBypassesModportRestrictionFromContainingScope_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
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
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
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

TEST(InterfaceObjectAccessElaboration,
     PortMemberReadOfSignalInModport_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
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
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfaceObjectAccessElaboration,
     PortMemberWriteToSignalNotListedInModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface ebus_i;\n"
      "  integer I;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  initial i.I = 0;\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfaceObjectAccessElaboration,
     PortMemberAccessToInterfaceTypedef_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
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
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
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

TEST(InterfaceObjectAccessElaboration,
     PortMemberAccessToInterfaceParameter_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
      "  parameter WIDTH = 8;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  integer P;\n"
      "  initial P = i.WIDTH;\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessElaboration,
     VifMemberAccessToSignalInModport_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
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
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfaceObjectAccessElaboration,
     VifMemberAccessToInterfaceLocalparam_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
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

TEST(InterfaceObjectAccessElaboration,
     HierarchicalReadOfNonListableLocalparamThroughModportBoundInterface_Ok) {
  EXPECT_TRUE(ElabOk(
      "interface ebus_i;\n"
      "  localparam True = 1;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "  integer P;\n"
      "  initial P = top.ebus.True;\n"
      "endmodule\n"));
}

}  // namespace
