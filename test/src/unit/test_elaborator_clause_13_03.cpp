// §13.3: Tasks


#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// Elaboration: task declaration within module
// ---------------------------------------------------------------------------
TEST(ParserA27, ElabTaskDeclInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task(input int a);\n"
      "    $display(\"a=%0d\", a);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
