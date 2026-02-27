// §11.4.6: Wildcard equality operators

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA86, BinaryWildcardEqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryWildcardNeqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
