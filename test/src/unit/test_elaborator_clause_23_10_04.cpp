// §23.10.4

#include "fixture_elaborator.h"

namespace {

TEST(BuildingBlockElaboration, AllModulesMapPopulated) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(design->all_modules.find("top"), design->all_modules.end());
  EXPECT_NE(design->all_modules.find("child"), design->all_modules.end());
}

}  // namespace
