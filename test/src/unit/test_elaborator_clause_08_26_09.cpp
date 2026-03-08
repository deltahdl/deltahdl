

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA8269, InterfaceClassNoConstraintsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}
