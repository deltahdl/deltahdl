// §8.4: Objects (class instance)

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § primary — null elaborates
TEST(ElabA84, PrimaryNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
