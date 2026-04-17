#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GenericInterfaceModportInstantiation, PositionalBindingWithModportSelector) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus;\n"
             "  logic req, gnt;\n"
             "  modport target(input req, output gnt);\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "endmodule\n"
             "module top;\n"
             "  simple_bus sb_intf();\n"
             "  memMod mem(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(GenericInterfaceModportInstantiation, NamedBindingWithModportSelector) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus;\n"
             "  logic req, gnt;\n"
             "  modport target(input req, output gnt);\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "endmodule\n"
             "module top;\n"
             "  simple_bus sb_intf();\n"
             "  memMod mem(.a(sb_intf.target));\n"
             "endmodule\n"));
}

TEST(GenericInterfaceModportInstantiation, TwoGenericPortsWithDifferentModports) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus;\n"
             "  logic req, gnt;\n"
             "  modport target(input req, output gnt);\n"
             "  modport initiator(output req, input gnt);\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "endmodule\n"
             "module cpuMod(interface b);\n"
             "endmodule\n"
             "module top;\n"
             "  simple_bus sb_intf();\n"
             "  memMod mem(sb_intf.target);\n"
             "  cpuMod cpu(sb_intf.initiator);\n"
             "endmodule\n"));
}

TEST(GenericInterfaceModportInstantiation, AcceptsAnyInterfaceTypeWithModport) {
  EXPECT_TRUE(
      ElabOk("interface bus_a;\n"
             "  logic d;\n"
             "  modport m(input d);\n"
             "endinterface\n"
             "interface bus_b;\n"
             "  logic d;\n"
             "  modport m(output d);\n"
             "endinterface\n"
             "module child(interface p);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_a i1();\n"
             "  bus_b i2();\n"
             "  child u1(i1.m);\n"
             "  child u2(i2.m);\n"
             "endmodule\n"));
}

}  // namespace
