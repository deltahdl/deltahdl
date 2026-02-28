// §13.3.1: Static and automatic tasks


#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA27, ElabTaskAutomaticLifetime) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic my_task(input int n);\n"
      "    #10;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
