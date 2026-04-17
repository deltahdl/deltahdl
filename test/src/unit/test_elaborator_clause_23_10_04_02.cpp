#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefparamEarlyNameResolution, AmbiguityWithNamedGenerateBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  m1 n();\n"
      "endmodule\n"
      "module m1;\n"
      "  parameter p = 2;\n"
      "  defparam m.n.p = 1;\n"
      "  if (p == 1) begin : m\n"
      "    m2 n();\n"
      "  end\n"
      "endmodule\n"
      "module m2;\n"
      "  parameter p = 3;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DefparamEarlyNameResolution, RenamedGenerateBlockRemovesAmbiguity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  m1 n();\n"
      "endmodule\n"
      "module m1;\n"
      "  parameter p = 2;\n"
      "  defparam m.n.p = 1;\n"
      "  if (p == 1) begin : gen_unique\n"
      "    m2 n();\n"
      "  end\n"
      "endmodule\n"
      "module m2;\n"
      "  parameter p = 3;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
