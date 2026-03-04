#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabCh511, ArrayInitPattern_FlatIllegal) {

  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}
