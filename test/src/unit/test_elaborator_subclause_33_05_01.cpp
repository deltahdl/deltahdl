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
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// §33.5.1 finishes the single-pass use model at the point the design is built:
// once every cell named on the command line has been compiled, the tool
// locates the top-level cell (§23.3.1) and proceeds down the hierarchy binding
// each instance as it meets it, and only the descriptions named on that
// command line are available to bind against.
//
// The input these tests drive is the one the clause describes -- source files
// on disk, mapped to libraries by a §33.3.1 library map, compiled by the
// single-pass precompiler -- rather than a compilation unit assembled by hand,
// because what these rules turn on is precisely how the unit was produced.

// The shared infrastructure a compile and the elaboration after it work on.
struct BindHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

// The descriptions of a two-deep hierarchy, one cell per file: top
// instantiates mid, mid instantiates leaf, leaf instantiates nothing.
struct HierarchySources {
  fs::path top;
  fs::path mid;
  fs::path leaf;
};

// Writes the hierarchy and the library map that claims it. The files are
// written leaf first, so the order they are created in cannot be mistaken for
// the order a command line names them in.
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

// ---------------------------------------------------------------------------
// Claim: after all the cells on the command line have been compiled, the tool
// locates the top-level cell and proceeds down the hierarchy, binding each
// instance as it is encountered.
// ---------------------------------------------------------------------------

TEST(SinglePassBinding, TopIsLocatedOnceTheWholeCommandLineIsCompiled) {
  // The command line names the leaf first and the top last. Were the top-level
  // cell sought while the descriptions were still being compiled, leaf -- the
  // only cell in the library at that moment, and instantiated by nothing yet
  // compiled -- would be taken for it.
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
  // No instance in top names leaf; it is reached only by descending through
  // mid, so its presence is what shows the walk continued past the top's own
  // children.
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
  // A precompile maps a cell into the library whether the design uses it or
  // not, and a cell no instance names is a top-level cell by §23.3.1. So a
  // spare description on the command line roots a hierarchy beside the
  // intended one rather than being discarded for going uninstantiated.
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

// ---------------------------------------------------------------------------
// Claim: only the source descriptions provided on the command line can be used
// to bind cell instances in the current design.
// ---------------------------------------------------------------------------

TEST(SinglePassBinding, CellHeldInTheLibraryOffThisCommandLineStillCannotBind) {
  // leaf.v sits on disk beside the other two and the library map claims it
  // just as readily, and an earlier command line has already compiled it: its
  // cell is in rtlLib right now, as the test asserts before elaborating. What
  // binds is nevertheless the descriptions this command line named, and this
  // one does not name leaf.v, so mid's instance of leaf is unbound. Omitting a
  // description the library has never heard of would prove less, because a
  // binder that consulted the library instead would fail that case too and
  // pass this one.
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
  // mid.v instantiates leaf on its own second line, and that instance is what
  // finds nothing to bind against.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(), "unknown module 'leaf'", 2,
                            "23.3.2"));
}

TEST(SinglePassBinding, HierarchySpanningTwoLibrariesBindsFromBoth) {
  // The descriptions on one command line need not share a library. The top
  // comes from one and the cell it instantiates from another, so the descent
  // has to cross the library boundary to bind the child at all.
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
  // The descent binds instances, not cell names. top holds two instances of
  // one cell and one of another, so a walk that bound a cell once and moved on
  // would leave the second child of that cell unresolved while still reporting
  // every module in the design.
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

// ---------------------------------------------------------------------------
// Claim: a cell already in the library from an unchanged description need not
// be recompiled -- which cannot mean it drops out of what the design binds
// against.
// ---------------------------------------------------------------------------

TEST(SinglePassBinding, DesignStillBindsWhenEveryCellIsUpToDate) {
  ScratchDir tmp;
  auto s = WriteHierarchy(tmp);

  BindHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({s.leaf, s.mid, s.top}, h.unit));

  // The same descriptions a second time: nothing has changed on disk, so every
  // cell is already in its library and none of them is compiled again.
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
