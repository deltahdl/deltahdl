// §5.11: Array literals

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §5.11: Array literals ---
TEST(ElabCh511, ArrayInitPattern_FlatIllegal) {
  // §5.11: Nesting of braces shall follow the number of dimensions.
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
