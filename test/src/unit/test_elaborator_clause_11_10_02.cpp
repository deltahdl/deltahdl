#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §11.10.2: String literal to wider vector elaborates.
TEST(Elaboration, StringPaddingWiderVectorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.10.2: Padded concat comparison elaborates.
TEST(Elaboration, PaddedConcatCompareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*10:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    result = ({s1, s2} == \"Hello world!\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
