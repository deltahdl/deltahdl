#include <gtest/gtest.h>

#include <filesystem>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct BindHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

struct HierarchySources {
  fs::path top;
  fs::path mid;
  fs::path leaf;
};

HierarchySources WriteHierarchy(ScratchDir& tmp) {
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  HierarchySources s;
  s.leaf = tmp.Write("src/leaf.v",
                     "module leaf;\n"
                     "endmodule\n");
  s.mid = tmp.Write("src/mid.v",
                    "module mid;\n"
                    "  leaf l();\n"
                    "endmodule\n");
  s.top = tmp.Write("src/top.v",
                    "module top;\n"
                    "  mid m();\n"
                    "endmodule\n");
  return s;
}

TEST(SinglePassBinding, TopIsLocatedOnceTheWholeCommandLineIsCompiled) {
  ScratchDir tmp;
  auto s = WriteHierarchy(tmp);

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({s.leaf, s.mid, s.top}, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = elab.Elaborate("");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(SinglePassBinding, EachInstanceBindsAsTheHierarchyIsDescended) {
  ScratchDir tmp;
  auto s = WriteHierarchy(tmp);

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({s.leaf, s.mid, s.top}, h.unit));

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = elab.Elaborate("");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(SinglePassBinding, CellNoInstanceNamesIsATopOfItsOwn) {
  ScratchDir tmp;
  auto s = WriteHierarchy(tmp);
  auto spare = tmp.Write("src/spare.v",
                         "module spare;\n"
                         "endmodule\n");

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.leaf, s.mid, s.top, spare};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = elab.Elaborate("");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "spare");
}

TEST(SinglePassBinding, CellHeldInTheLibraryOffThisCommandLineStillCannotBind) {
  ScratchDir tmp;
  auto s = WriteHierarchy(tmp);

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  CompilationUnit earlier;
  ASSERT_TRUE(h.compiler.CompileCommandLine({s.leaf}, earlier));
  ASSERT_NE(h.libs.CellInLibrary("rtlLib", "leaf"), nullptr);

  ASSERT_TRUE(h.compiler.CompileCommandLine({s.mid, s.top}, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  elab.Elaborate("");
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(), "unknown module 'leaf'", 2,
                            "23.3.2"));
}

TEST(SinglePassBinding, HierarchySpanningTwoLibrariesBindsFromBoth) {
  ScratchDir tmp;
  tmp.Write("lib.map",
            "library rtlLib rtl/*.v;\n"
            "library gateLib gate/*.vg;\n");
  auto gate = tmp.Write("gate/adder.vg",
                        "module adder;\n"
                        "endmodule\n");
  auto top = tmp.Write("rtl/top.v",
                       "module top;\n"
                       "  adder a1();\n"
                       "endmodule\n");

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({gate, top}, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = elab.Elaborate("");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_TRUE(design->all_modules.contains("adder"));
}

TEST(SinglePassBinding, EveryInstanceMetIsBoundNotOnlyTheFirstOfACell) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto child = tmp.Write("src/child.v",
                         "module child;\n"
                         "endmodule\n");
  auto other = tmp.Write("src/other.v",
                         "module other;\n"
                         "endmodule\n");
  auto top = tmp.Write("src/top.v",
                       "module top;\n"
                       "  child c1();\n"
                       "  child c2();\n"
                       "  other o1();\n"
                       "endmodule\n");

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{child, other, top};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = elab.Elaborate("");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_EQ(design->top_modules[0]->children.size(), 3u);
  EXPECT_EQ(design->top_modules[0]->children[0].inst_name, "c1");
  EXPECT_NE(design->top_modules[0]->children[0].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[1].inst_name, "c2");
  EXPECT_NE(design->top_modules[0]->children[1].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[2].inst_name, "o1");
  EXPECT_NE(design->top_modules[0]->children[2].resolved, nullptr);
}

TEST(SinglePassBinding, DesignStillBindsWhenEveryCellIsUpToDate) {
  ScratchDir tmp;
  auto s = WriteHierarchy(tmp);

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({s.leaf, s.mid, s.top}, h.unit));

  CompilationUnit rerun;
  ASSERT_EQ(h.compiler.CompileSource(s.leaf, rerun), CompileOutcome::kSkipped);
  ASSERT_EQ(h.compiler.CompileSource(s.mid, rerun), CompileOutcome::kSkipped);
  ASSERT_EQ(h.compiler.CompileSource(s.top, rerun), CompileOutcome::kSkipped);

  Elaborator elab(h.arena, h.diag, &rerun);
  auto* design = elab.Elaborate("");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

}  // namespace
