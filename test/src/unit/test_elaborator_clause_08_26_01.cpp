#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassImplElaboration, InterfaceClassDeclOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void do_thing();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
