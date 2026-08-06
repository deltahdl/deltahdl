#include "fixture_elaborator.h"
#include "helpers_include_test_dir.h"

using namespace delta;

namespace {

static RtlirDesign* ElaborateWithIncludes(IncludeTestDir& tmp,
                                          const std::string& main_src,
                                          ElabFixture& f,
                                          std::string_view top = "") {
  tmp.WriteFile("main.sv", main_src);
  auto fid = f.mgr.AddFile((tmp.dir / "main.sv").string(), main_src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  cu->default_nettype = preproc.DefaultNetType();
  PropagateDecayAndDelayToCu(cu, preproc);
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  auto* design = elab.Elaborate(name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

TEST(IncludeFileElaboration, IncludedParameterElaboratesCorrectly) {
  IncludeTestDir tmp;
  tmp.WriteFile("params.svh", "`define SIZE 32\n");

  ElabFixture f;
  auto* design = ElaborateWithIncludes(tmp,
                                       "`include \"params.svh\"\n"
                                       "module t;\n"
                                       "  parameter P = `SIZE;\n"
                                       "endmodule\n",
                                       f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 32);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(IncludeFileElaboration, NestedIncludeParameterElaborates) {
  IncludeTestDir tmp;
  tmp.WriteFile("base.svh", "`define BASE_VAL 10\n");
  tmp.WriteFile("derived.svh",
                "`include \"base.svh\"\n"
                "`define DERIVED_VAL (`BASE_VAL * 2)\n");

  ElabFixture f;
  auto* design = ElaborateWithIncludes(tmp,
                                       "`include \"derived.svh\"\n"
                                       "module t;\n"
                                       "  parameter P = `DERIVED_VAL;\n"
                                       "endmodule\n",
                                       f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 20);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(IncludeFileElaboration, IncludedDirectiveAffectsElaboration) {
  IncludeTestDir tmp;
  tmp.WriteFile("setup.svh", "`delay_mode_zero\n");

  ElabFixture f;
  auto* design = ElaborateWithIncludes(tmp,
                                       "`include \"setup.svh\"\n"
                                       "module t;\n"
                                       "  parameter P = 1;\n"
                                       "endmodule\n",
                                       f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kZero);
}

}  // namespace
