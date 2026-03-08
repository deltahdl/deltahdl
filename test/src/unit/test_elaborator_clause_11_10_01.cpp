#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §11.10.1: Copy — string literal assignment to vector elaborates successfully.
TEST(Elaboration, StringLiteralCopyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*5:1] s;\n"
      "  initial s = \"Hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.10.1: Concatenate — concatenation of string vectors elaborates.
TEST(Elaboration, StringLiteralConcatElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*14:1] s;\n"
      "  initial begin\n"
      "    s = \"Hello world\";\n"
      "    s = {s, \"!!!\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.10.1: Compare — equality of string vectors elaborates.
TEST(Elaboration, StringLiteralCompareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*5:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \"Hello\";\n"
      "    result = (s1 == s2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.10.1: String literal to wider vector (zero-padding) elaborates.
TEST(Elaboration, StringLiteralWiderVectorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hi\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
