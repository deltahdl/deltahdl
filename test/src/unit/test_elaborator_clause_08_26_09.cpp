// Non-LRM tests

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.9: Interface class without constraint blocks — OK.
TEST(ElabA8269, InterfaceClassNoConstraintsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
