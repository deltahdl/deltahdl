// §11.9: Tagged union expressions and member access

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § tagged_union_expression — tagged elaborates
TEST(ElabA83, TaggedUnionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = tagged Valid 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
