#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InterfaceObjectAccessParsing,
     HierarchicalReferenceToInterfaceSignalInProcedural) {
  EXPECT_TRUE(ParseOk(
      "interface ebus_i;\n"
      "  integer I;\n"
      "endinterface\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  initial top.ebus.I = 0;\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessParsing,
     PortMemberAccessToInterfaceSignalInContinuousAssign) {
  EXPECT_TRUE(ParseOk(
      "interface ebus_i;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  logic P;\n"
      "  assign P = i.Q;\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessParsing,
     PortMemberAccessToInterfaceTypedefUsedAsType) {
  EXPECT_TRUE(ParseOk(
      "interface ebus_i;\n"
      "  typedef enum {Y, N} choice;\n"
      "  choice Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  typedef i.choice yes_no;\n"
      "  yes_no P;\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessParsing,
     PortMemberAccessToInterfaceLocalparamInExpression) {
  EXPECT_TRUE(ParseOk(
      "interface ebus_i;\n"
      "  logic Q;\n"
      "  localparam True = 1;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  logic P;\n"
      "  initial P = i.True;\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessParsing,
     HierarchicalWriteCoexistsWithPortReferenceInSameModule) {
  EXPECT_TRUE(ParseOk(
      "interface ebus_i;\n"
      "  integer I;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "endmodule\n"
      "module sub(ebus_i.mp i);\n"
      "  logic P;\n"
      "  assign P = i.Q;\n"
      "  initial top.ebus.I = 0;\n"
      "endmodule\n"));
}

TEST(InterfaceObjectAccessParsing,
     InterfacePortDeclarationWithModportSelector) {
  auto r = Parse(
      "interface ebus_i;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
