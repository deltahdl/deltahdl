#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceModportInstantiation, PositionalBindingWithModportSelector) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus;\n"
             "  logic req, gnt;\n"
             "  modport target(input req, output gnt);\n"
             "  modport initiator(output req, input gnt);\n"
             "endinterface\n"
             "module memMod(simple_bus a);\n"
             "endmodule\n"
             "module top;\n"
             "  simple_bus sb_intf();\n"
             "  memMod mem(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(InterfaceModportInstantiation, NamedBindingWithModportSelector) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus;\n"
             "  logic req, gnt;\n"
             "  modport target(input req, output gnt);\n"
             "endinterface\n"
             "module memMod(simple_bus a);\n"
             "endmodule\n"
             "module top;\n"
             "  simple_bus sb_intf();\n"
             "  memMod mem(.a(sb_intf.target));\n"
             "endmodule\n"));
}

TEST(InterfaceModportInstantiation, TwoInstancesWithDifferentModports) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus;\n"
             "  logic req, gnt;\n"
             "  modport target(input req, output gnt);\n"
             "  modport initiator(output req, input gnt);\n"
             "endinterface\n"
             "module memMod(simple_bus a);\n"
             "endmodule\n"
             "module cpuMod(simple_bus b);\n"
             "endmodule\n"
             "module top;\n"
             "  simple_bus sb_intf();\n"
             "  memMod mem(sb_intf.target);\n"
             "  cpuMod cpu(sb_intf.initiator);\n"
             "endmodule\n"));
}

TEST(InterfaceModportInstantiation, WrongInterfaceTypeWithModportSelectorErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus;\n"
      "  logic data;\n"
      "  modport target(input data);\n"
      "endinterface\n"
      "interface other_if;\n"
      "  logic data;\n"
      "  modport target(input data);\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "endmodule\n"
      "module top;\n"
      "  other_if sb_intf();\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
