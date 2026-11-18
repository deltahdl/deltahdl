#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
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

TEST(InterfaceObjectAccessElaboration,
     GenericModportPortAccessOutsideModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface ebus_i;\n"
      "  integer I;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(interface.mp i);\n"
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

TEST(InterfaceObjectAccessElaboration,
     GenericModportPortListedAccessElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "interface ebus_i;\n"
      "  integer I;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(interface.mp i);\n"
      "  logic P;\n"
      "  initial P = i.Q;\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(InterfacePortTypedef, TypedefsNoInterfaceAnswersElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc; typedef enum {Y, N} choice; endinterface\n"
      "module gen(interface i); typedef i.choice t1; endmodule\n"
      "module miss(ifc i); typedef i.other t2; endmodule\n"
      "module none(ifc i); typedef j.choice t3; endmodule\n"
      "module top; ifc x(); gen g(x); miss m(x); none n(x); endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->top_modules[0]->children.size(), 4u);
}

constexpr const char* kDollarMsg =
    "'$' may stand only in a queue's dimension or select, a value range's "
    "bound, a cycle delay range's upper bound, a sequence, property or checker "
    "argument, or a parameter's value";

constexpr const char* kGenericPortInterfaces =
    "interface ia; typedef int IT [$]; endinterface\n"
    "interface ib; typedef int IT [2]; endinterface\n"
    "module m (interface i);\n"
    "  typedef i.IT T1;\n"
    "  T1 v;\n"
    "  initial $display(\"%0d\", v[$]);\n"
    "endmodule\n";

TEST(GenericPortTypedefElaboration,
     DISABLED_ADollarSelectOfAFixedArrayTakenThroughAGenericPortIsRefused) {
  ElabFixture f;
  ElaborateSrc(std::string(kGenericPortInterfaces) +
                   "module top; ib b(); m ub(b); endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDollarMsg, 6, "6.20.7"));
}

TEST(GenericPortTypedefElaboration,
     DISABLED_ADollarSelectOfAQueueTakenThroughAGenericPortIsAccepted) {
  ElabFixture f;
  ElaborateSrc(std::string(kGenericPortInterfaces) +
                   "module top; ia a(); m ua(a); endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
