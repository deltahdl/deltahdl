#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.5: Event variable elaborates with is_event flag set.
TEST(NamedEventElaborator, DeclarationSetsIsEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_event);
}

// §15.5: Event variable has width 0 (singular type, not aggregate).
TEST(NamedEventElaborator, EventWidthIsZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 0u);
}

// §15.5: Multiple event declarations each elaborate correctly.
TEST(NamedEventElaborator, MultipleEventDeclarations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event done;\n"
      "  event blast;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_TRUE(mod->variables[0].is_event);
  EXPECT_TRUE(mod->variables[1].is_event);
}

// §15.5: Event with initializer elaborates without error.
TEST(NamedEventElaborator, EventWithInitializer) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n"));
}

// §15.5: Event assigned null elaborates without error.
TEST(NamedEventElaborator, EventAssignedNull) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev = null;\n"
      "endmodule\n"));
}

}  // namespace
