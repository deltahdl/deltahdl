

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassInheritElaboration, InterfaceClassNoConstraintsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
