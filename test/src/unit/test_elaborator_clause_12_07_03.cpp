// §12.7.3: The foreach-loop

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §12.7.3: foreach loop elaborates without error
TEST(ElabA608, ForeachLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
