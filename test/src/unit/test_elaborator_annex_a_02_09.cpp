#include "fixture_elaborator.h"

namespace {

TEST(ModportDeclarationElaboration, SimpleModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, MultipleModportsElaborate) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  logic req, gnt;\n"
             "  modport master(output req, input gnt);\n"
             "  modport slave(input req, output gnt);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, ImportExportModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  modport mp(import Read, export Write);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, MixedPortKindsElaborate) {
  EXPECT_TRUE(
      ElabOk("interface ifc(input logic clk);\n"
             "  logic req, gnt;\n"
             "  clocking cb @(posedge clk); endclocking\n"
             "  modport mp(\n"
             "    input req,\n"
             "    output gnt,\n"
             "    import Read,\n"
             "    clocking cb\n"
             "  );\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, TwoInterfacesWithModportsElaborate) {
  EXPECT_TRUE(
      ElabOk("interface bus_a;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "interface bus_b;\n"
             "  logic addr;\n"
             "  modport slave(input addr);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, CommaModportItemsElaborate) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  logic a, b;\n"
             "  modport m1(input a), m2(output b);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, ImportPrototypeElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  modport mp(\n"
             "    import function int compute(int a),\n"
             "    import task do_work(int x)\n"
             "  );\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
