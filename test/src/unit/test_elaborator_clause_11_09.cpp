#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(TaggedUnion, TagDefaultEmpty) {
  SimFixture f;
  EXPECT_TRUE(f.ctx.GetVariableTag("nonexistent").empty());
}

}  // namespace
