// §25.5

#include "fixture_elaborator.h"

namespace {

TEST(InterfaceModport, InterfaceWithModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceModport, MultipleModportsElaborate) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "  modport slave(input data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceModport, ModuleWithNamedInterfacePortAndModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "module m(bus.master b);\n"
             "endmodule\n"));
}

TEST(InterfaceModport, ModuleWithGenericInterfacePortAndModportElaborates) {
  EXPECT_TRUE(
      ElabOk("module m(interface.master b);\n"
             "endmodule\n"));
}

}  // namespace
