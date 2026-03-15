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

}  // namespace
