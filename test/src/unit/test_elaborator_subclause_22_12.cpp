#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_scratch_dir.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

TEST(LineDirectiveElaboration, OverriddenLineSizesElaboratedVector) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  `line 40 \"renamed.sv\" 0\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 40u);
}

TEST(LineDirectiveElaboration,
     OverrideBetweenModulesRenumbersElaboratedVector) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module m1;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "`line 60 \"switched.sv\" 0\n"
      "module t;\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 61u);
}

struct MappedSource {
  std::string name;
  std::string text;
};

struct MappedDesign {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap map;
  CompilationUnit* unit = nullptr;
};

bool AssembleMapped(ScratchDir& tmp, MappedDesign& d,
                    const std::vector<MappedSource>& files) {
  auto map_path = tmp.Write("lib.map",
                            "library work t.sv;\n"
                            "library libA a.sv;\n"
                            "library libB b.sv;\n");
  if (!d.map.LoadMapFile(map_path)) return false;
  Preprocessor pp(d.mgr, d.diag, {});
  for (const auto& file : files) {
    auto path = tmp.Write(file.name, file.text).string();
    auto out = pp.Preprocess(d.mgr.AddFile(path, file.text));
    auto fid =
        d.mgr.AddPreprocessedFile("<preprocessed>", out, pp.LineOrigins());
    Lexer lexer(d.mgr.FileContent(fid), fid, d.diag,
                TextOrigin::kPreprocessorOutput);
    Parser parser(lexer, d.arena, d.diag);
    auto* cu = parser.Parse();
    if (cu == nullptr || d.diag.HasErrors()) return false;
    d.map.TagCompilationUnit(*cu, path);
    if (d.unit == nullptr) {
      d.unit = cu;
      continue;
    }
    d.unit->modules.insert(d.unit->modules.end(), cu->modules.begin(),
                           cu->modules.end());
    d.unit->configs.insert(d.unit->configs.end(), cu->configs.begin(),
                           cu->configs.end());
  }
  return d.unit != nullptr;
}

std::string LibraryBoundUnder(const char* liblist) {
  ScratchDir tmp;
  MappedDesign d;
  std::vector<MappedSource> files = {
      {"a.sv", "`line 1 \"b.sv\" 0\nmodule leaf;\nendmodule\n"},
      {"b.sv", "module leaf;\nendmodule\n"},
      {"t.sv", std::string("module t;\n  leaf u();\nendmodule\n"
                           "config cfg;\n  design work.t;\n"
                           "  default liblist ") +
                   liblist + ";\nendconfig\n"},
  };
  if (!AssembleMapped(tmp, d, files)) return "<not assembled>";
  Elaborator elab(d.arena, d.diag, d.unit);
  std::vector<std::string> order;
  for (auto name : d.map.LibraryDeclarationOrder()) order.emplace_back(name);
  elab.SetLibraryDeclarationOrder(order);
  auto* design = elab.Elaborate(d.unit->configs.front());
  if (design == nullptr || design->top_modules.size() != 1u) {
    return "<not elaborated>";
  }
  for (const auto& child : design->top_modules[0]->children) {
    if (child.inst_name == "u" && child.resolved != nullptr) {
      return std::string(child.resolved->library);
    }
  }
  return "<unbound>";
}

TEST(LineDirectiveElaboration, AFileKeepsItsMappedLibraryUnderAnOverride) {
  EXPECT_EQ(LibraryBoundUnder("libA"), "libA");
  EXPECT_EQ(LibraryBoundUnder("libB"), "libB");
}

}  // namespace
