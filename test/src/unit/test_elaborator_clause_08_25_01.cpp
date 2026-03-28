#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodElaboration, ValueParamScopeOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
