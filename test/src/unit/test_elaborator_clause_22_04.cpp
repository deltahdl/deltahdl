#include <cstdlib>
#include <filesystem>
#include <fstream>

#include "fixture_elaborator.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct IncludeTestDir {
  fs::path dir;
  IncludeTestDir() {
    dir =
        fs::temp_directory_path() / ("delta_test_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }
  ~IncludeTestDir() { fs::remove_all(dir); }
  fs::path WriteFile(const std::string& rel, const std::string& content) {
    auto full = dir / rel;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

static RtlirDesign* ElaborateWithIncludes(IncludeTestDir& tmp,
                                          const std::string& main_src,
                                          ElabFixture& f,
                                          std::string_view top = "") {
  tmp.WriteFile("main.sv", main_src);
  auto fid = f.mgr.AddFile((tmp.dir / "main.sv").string(), main_src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->default_nettype = preproc.DefaultNetType();
  cu->default_decay_time = preproc.DefaultDecayTime();
  cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  cu->default_trireg_strength = preproc.DefaultTriregStrength();
  cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  cu->delay_mode_directive = preproc.DelayModeDirective();
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
