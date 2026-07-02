

#include "fixture_elaborator.h"

namespace {

TEST(TopLevelModules, EmptySourceTopNotFoundReturnsNull) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("top");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(TopLevelModules, ElaboratedDesignContainsTopModule) {
  ElabFixture f;
  auto* design = ElaborateSrc("module top; endmodule", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(TopLevelModules, SelectSpecificTopFromMultipleModules) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n",
      f, "b");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "b");
}

TEST(TopLevelModules, NonexistentTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n",
      f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

bool HasTopNamed(const RtlirDesign* design, std::string_view name) {
  for (auto* m : design->top_modules)
    if (m->name == name) return true;
  return false;
}

// §23.3.1: with no explicit top named, every module that does not appear in any
// module instantiation statement is implicitly instantiated once as a top-level
// module. Two mutually independent modules therefore both become tops. This is
// the auto-top path (§23.3.1) that a named-top elaboration bypasses.
TEST(TopLevelModules, AutoTopRootsEveryUninstantiatedModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a; endmodule\n"
      "module b; endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_TRUE(HasTopNamed(design, "a"));
  EXPECT_TRUE(HasTopNamed(design, "b"));
}

// §23.3.1: a design shall contain at least one top-level module. When every
// declared module is instantiated by another -- here `a` and `b` instantiate
// each other, so neither is a root -- the auto-top path finds no top-level
// module and the elaborator reports the malformed design rather than silently
// yielding an empty one.
TEST(TopLevelModules, DesignWithNoTopLevelModuleIsError) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a;\n"
      "  b b1();\n"
      "endmodule\n"
      "module b;\n"
      "  a a1();\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §23.3.1: a module that appears in a module instantiation statement does not
// become a top-level module. Only `top` is rooted; the instantiated `child` is
// excluded from the auto-top set.
TEST(TopLevelModules, AutoTopExcludesNormallyInstantiatedChild) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

// §23.3.1 (interweave with §27.3/§3.12): the top-level exclusion applies even
// when the sole instantiation sits in a generate block that is not itself
// instantiated. `child`'s only instantiation is inside a generate-if whose
// constant condition is false (§27.3: generate schemes are evaluated during
// elaboration, §3.12), so that block produces zero instances -- yet the textual
// appearance still disqualifies `child` from being a top-level module. Only
// `wrapper` is rooted. Removing the generate-body descent in the instantiation
// collector would wrongly promote `child` to a second top.
TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateIf) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  if (0) begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

// §23.3.1 (interweave with §27.3): the disqualifying instantiation may live in
// the else arm of a generate-if. The selected arm here contains no
// instantiation, so `child` is never elaborated into the hierarchy, but its
// textual appearance in the unselected else block still keeps it out of the
// auto-top set. Exercises the gen_else branch of the instantiation collector.
TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateElse) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  if (1) begin\n"
      "    logic keep;\n"
      "  end else begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

// §23.3.1 (interweave with §27.3): the disqualifying instantiation may live in
// a case-generate item that the constant selector does not choose. `SEL`
// selects the default arm, so the `0:` arm holding `child` is never
// instantiated, yet its textual appearance still excludes `child` from the
// auto-top set. Exercises the gen_case_items branch of the instantiation
// collector.
TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateCase) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  parameter SEL = 9;\n"
      "  case (SEL)\n"
      "    0: begin\n"
      "      child c1();\n"
      "    end\n"
      "    default: begin\n"
      "      logic keep;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

// §23.3.1 (interweave with §27.3): the disqualifying instantiation may sit in a
// loop-generate body, a distinct syntactic position from the conditional forms.
// `child`'s only instantiation is the loop body, so its textual appearance
// keeps it out of the auto-top set even though the loop instantiates it under
// `wrapper`. Exercises the loop-generate gen_body descent of the collector.
TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateFor) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

TEST(TopLevelModules, DollarRootRefResolvesToTopInstance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module top;\n"
      "  logic [7:0] x;\n"
      "  assign x = $root.top.x;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TopLevelModules, DollarRootMultiLevelPathResolves) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic x;\n"
      "  assign x = $root.top.c1.sig;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
