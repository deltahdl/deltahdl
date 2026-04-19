#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MinTypMaxElaboration, SpecparamConstantMinTypMax) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam tpd = 1:2:3;\n"
      "  endspecify\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
