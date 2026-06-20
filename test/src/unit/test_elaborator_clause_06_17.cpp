#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, EventVarIsEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "ev") {
      found = true;
      EXPECT_TRUE(v.is_event);
    }
  }
  EXPECT_TRUE(found) << "event variable 'ev' not found";
}

TEST(Elaboration, EventVarWidthZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "ev") {
      EXPECT_EQ(v.width, 0u);
    }
  }
}

TEST(Elaboration, EventAssignNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, MultipleEventDeclarationsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int event_count = 0;
  for (const auto& v : mod->variables) {
    if (v.is_event) ++event_count;
  }
  EXPECT_EQ(event_count, 2);
}

TEST(Elaboration, EventAliasInitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  const RtlirVariable* done_too = nullptr;
  for (const auto& v : mod->variables) {
    if (v.name == "done_too") done_too = &v;
  }
  ASSERT_NE(done_too, nullptr);
  EXPECT_TRUE(done_too->is_event);
  ASSERT_NE(done_too->init_expr, nullptr);
  EXPECT_EQ(done_too->init_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(done_too->init_expr->text, "done");
}

}  // namespace
