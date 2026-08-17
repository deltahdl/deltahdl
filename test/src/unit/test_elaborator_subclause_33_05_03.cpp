#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"
#include "parser/precompiled_library.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// §33.5.3 puts compiling and binding in separate tools. A compiler invocation
// leaves each cell it compiles in a compiled form in the filesystem, and the
// tool that binds the design afterwards is told the name of each top-level cell
// and nothing else: it reads the subinstances of a cell out of that cell's
// precompiled form and descends on what it finds, and every cell it will ever
// see has to be in a library before it starts.
//
// These tests keep the two tools apart. Every cell reaches a bind the way the
// clause says it does -- as real source given to a precompile, written to a
// file, and read back off that file by a binder holding nothing else -- rather
// than as a compilation unit a test assembled, because what these rules turn on
// is precisely that the binder never sees a source description.

// The infrastructure one bind runs against. A fresh instance shares nothing
// with the precompiles that wrote the libraries it reads.
struct BindHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  SeparateCompilationBinder binder{mgr, arena, diag};
};

// One invocation of the compiler tool: compiles `source` into library
// `library`, held in the compiled form kept at `path`.
void Precompile(const std::string& source, const std::string& library,
                const fs::path& path) {
  ASSERT_TRUE(PrecompiledLibrary::Save(source, library, path));
}

// A two-deep hierarchy, one cell per source description: top instantiates mid,
// mid instantiates leaf, leaf instantiates nothing.
constexpr const char* kLeaf =
    "module leaf;\n"
    "endmodule\n";
constexpr const char* kMid =
    "module mid;\n"
    "  leaf l();\n"
    "endmodule\n";
constexpr const char* kTop =
    "module top;\n"
    "  mid m();\n"
    "endmodule\n";

// A second top-level cell over the same leaf, and a cell no hierarchy reaches.
constexpr const char* kOther =
    "module other;\n"
    "  leaf l();\n"
    "endmodule\n";
constexpr const char* kSpare =
    "module spare;\n"
    "endmodule\n";

// One cell instantiating another twice.
constexpr const char* kTwice =
    "module twice;\n"
    "  leaf l1();\n"
    "  leaf l2();\n"
    "endmodule\n";

// A hierarchy whose two cells are compiled into two different libraries.
constexpr const char* kAdder =
    "module adder;\n"
    "endmodule\n";
constexpr const char* kAdderTop =
    "module adder_top;\n"
    "  adder a1();\n"
    "endmodule\n";

// One cell instantiating two others, neither of them ever compiled.
constexpr const char* kTwoMissing =
    "module two_missing;\n"
    "  gone_a a1();\n"
    "  gone_b b1();\n"
    "endmodule\n";

// A cell instantiating one cell a library holds and, on the line after it, one
// no library holds. The instantiation of gone stands on line 4 of this source,
// which is neither the line the declaration around it opens on nor the line the
// first instantiation stands on, so a report that named either of those instead
// of the instantiation it is about is legible as such.
constexpr const char* kMissingBelowAnother =
    "module missing_below_another;\n"
    "\n"
    "  leaf l();\n"
    "  gone g();\n"
    "endmodule\n";

// A cell whose only instance of leaf sits inside a generate alternative that
// the constant condition selects, so the instance is reached only by looking
// inside the generate.
constexpr const char* kGenerateTop =
    "module generate_top;\n"
    "  if (1) begin : g\n"
    "    leaf l();\n"
    "  end\n"
    "endmodule\n";

// A cell that declares the cell it instantiates inside its own body, so the
// instantiated name belongs to no library entry of its own.
constexpr const char* kDeclaresItsChild =
    "module declares_its_child;\n"
    "  module inner;\n"
    "  endmodule\n"
    "  inner i();\n"
    "endmodule\n";

// An interface, and a cell instantiating it.
constexpr const char* kInterface =
    "interface ifc;\n"
    "endinterface\n";
constexpr const char* kHoldsInterface =
    "module holds_interface;\n"
    "  ifc i();\n"
    "endmodule\n";

// A primitive, and a cell instantiating it.
constexpr const char* kPrimitive =
    "primitive ubuf(output o, input i);\n"
    "  table\n"
    "    0 : 0;\n"
    "    1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";
constexpr const char* kHoldsPrimitive =
    "module holds_primitive;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  ubuf u1(y, a);\n"
    "endmodule\n";

// ---------------------------------------------------------------------------
// Claim: the binding tool needs to be told only the top-level module(s) of the
// design to be bound.
// ---------------------------------------------------------------------------

TEST(SeparateCompilationBinding, TopIsBoundFromNothingButItsName) {
  // The binder is handed one name and one compiled form. No source description
  // reaches it -- not even the top's, which ran earlier through a compiler
  // invocation this one shares nothing with.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(SeparateCompilationBinding, EveryNamedTopRootsTheBoundDesign) {
  // A design may have more than one top-level cell, and the binder is told all
  // of them. Both hierarchies are rooted, in the order named.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);
  Precompile(kOther, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top", "other"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "other");
}

TEST(SeparateCompilationBinding, ATopNamedTwiceRootsOneHierarchy) {
  // Naming a cell twice says no more than naming it once did: it is a top of
  // this design. A binder taking the list at face value would root the same
  // hierarchy twice and report a design with two copies of everything under it.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top", "top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(SeparateCompilationBinding, NamingNoTopAtAllIsReported) {
  // The one thing this tool has to be told is which cells the tops are. Asked
  // to bind without being told, it says so rather than binding whatever the
  // library happens to hold.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({}), nullptr);
  // The report is about the invocation rather than about anything written in a
  // source description, so it stands at no position and enforces no subclause.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "no top-level module was named to elaborate", 0,
                            ""));
}

// ---------------------------------------------------------------------------
// Claim: the binding tool uses the precompiled form of the cell descriptions
// from the library to determine the subinstances and descends hierarchically
// down the design, binding each cell as it is located.
// ---------------------------------------------------------------------------

TEST(SeparateCompilationBinding, SubinstancesComeOutOfThePrecompiledForm) {
  // Nothing the binder is told names mid or leaf. mid is found by reading what
  // top's precompiled form instantiates, and leaf only by reading mid's, so
  // leaf's presence is what shows the descent continued past the top's own
  // children.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(SeparateCompilationBinding, EachInstanceMetIsBoundToItsPrecompiledCell) {
  // The descent binds instances, not cell names: a cell instantiated twice is
  // bound at both instances. Both instances are on one cell's precompiled form,
  // so what this checks is the binding rather than the walk.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kTwice, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"twice"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_EQ(design->top_modules[0]->children.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->children[0].inst_name, "l1");
  EXPECT_NE(design->top_modules[0]->children[0].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[1].inst_name, "l2");
  EXPECT_NE(design->top_modules[0]->children[1].resolved, nullptr);
}

TEST(SeparateCompilationBinding, CellInAGenerateIsBoundAsItIsLocated) {
  // An instance need not sit plainly among a cell's items. The one instance of
  // leaf in this design is inside a generate alternative, so reading the
  // precompiled form for subinstances has to look inside the generate to locate
  // it at all -- and having located it, the descent binds it like any other.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kGenerateTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"generate_top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(SeparateCompilationBinding, CellNoNamedTopReachesIsNotBound) {
  // A library holds whatever was compiled into it, which need not all belong to
  // the design being bound. The tops of this design are the ones the binder was
  // told, so a cell no descent from them reaches is left where it is instead of
  // rooting a hierarchy of its own.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);
  Precompile(kSpare, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_FALSE(design->all_modules.contains("spare"));
}

TEST(SeparateCompilationBinding, DescentCrossesFromOneCompiledFormToAnother) {
  // A design's cells need not have been compiled together. Two invocations of
  // the compiler tool wrote two forms under two library names here, and the
  // descent has to cross from one to the other to reach the child at all. The
  // library a bound cell came from survives the crossing.
  ScratchDir tmp;
  auto rtl = tmp.dir / "rtlLib.dpl";
  auto gate = tmp.dir / "gateLib.dpl";
  Precompile(kAdder, "gateLib", gate);
  Precompile(kAdderTop, "rtlLib", rtl);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(rtl));
  ASSERT_TRUE(h.binder.LoadLibrary(gate));
  auto* design = h.binder.Bind({"adder_top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_TRUE(design->all_modules.contains("adder"));
  EXPECT_EQ(design->all_modules.at("adder")->library, "gateLib");
}

// ---------------------------------------------------------------------------
// Claim: all cells in a design shall be precompiled prior to binding it.
// ---------------------------------------------------------------------------

TEST(SeparateCompilationBinding, CellBelowATopNeverCompiledStopsTheBind) {
  // top and mid were compiled; leaf, which mid instantiates, never was. No
  // source description can reach this tool, so nothing can supply leaf later
  // and the bind does not start.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"top"}), nullptr);
  // mid instantiates leaf on its own second line, and that instantiation is
  // where the design asks for the cell nobody compiled.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cell 'leaf' was not precompiled", 2, "33.5.3"));
}

TEST(SeparateCompilationBinding, TwoCellsMissingUnderOneTopAreBothNamed) {
  // The whole design is checked before any of it is bound, so a design short of
  // two cells is told about both. A tool that instead failed at the first
  // instance it could not bind would name one of them and leave the other to be
  // discovered on the next attempt.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kTwoMissing, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"two_missing"}), nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 2u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0].name, "gone_a");
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[1].name, "gone_b");
}

TEST(SeparateCompilationBinding, CellInAGenerateIsCheckedBeforeBinding) {
  // The check has to reach as far as the binding will. leaf is instantiated
  // only inside a generate alternative, so a check that read a cell's plain
  // items and stopped there would find nothing missing and let the bind start
  // on a design that cannot be completed.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kGenerateTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"generate_top"}), nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 1u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0].name, "leaf");
}

TEST(SeparateCompilationBinding, CellDeclaredInsideItsParentNeedsNoLibrary) {
  // A cell declared inside another travels in that cell's compiled form and has
  // no library entry of its own. The instance naming it is bound from something
  // that was compiled, so reporting it as absent would refuse a design in which
  // nothing is in fact missing.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kDeclaresItsChild, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  h.binder.Bind({"declares_its_child"});
  EXPECT_TRUE(h.binder.CellsNotPrecompiled().empty());
}

TEST(SeparateCompilationBinding, InterfaceHeldInALibraryCountsAsPrecompiled) {
  // An interface is a cell a compiler can hold and an instance can name, so a
  // check that recognised only modules and primitives would report this design
  // short of a cell its library is holding.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kInterface, "rtlLib", path);
  Precompile(kHoldsInterface, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  h.binder.Bind({"holds_interface"});
  EXPECT_TRUE(h.binder.CellsNotPrecompiled().empty());
}

TEST(SeparateCompilationBinding, TopNamedButNeverCompiledIsReportedByName) {
  // The restriction covers the tops as much as the cells beneath them: a
  // binding tool told the name of a cell no invocation of the compiler ever
  // reached has no design to bind.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"top"}), nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 1u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0].name, "top");
}

TEST(SeparateCompilationBinding, PrimitiveHeldInALibraryCountsAsPrecompiled) {
  // A primitive is a cell an instance can name and a compiler can hold, and it
  // holds no instances of its own. Finding one ends that branch of the descent
  // rather than being taken for a cell nobody compiled.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kPrimitive, "rtlLib", path);
  Precompile(kHoldsPrimitive, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  h.binder.Bind({"holds_primitive"});
  EXPECT_TRUE(h.binder.CellsNotPrecompiled().empty());
}

// ---------------------------------------------------------------------------
// Claim: the compiled forms persist in the filesystem, and are what a bind
// reads.
// ---------------------------------------------------------------------------

TEST(SeparateCompilationBinding, OneCompiledFormServesBindAfterBind) {
  // Reading a compiled form does not consume it. The second binder shares
  // nothing with the first -- its own source manager, arena and diagnostics --
  // and finds the same cells still in the filesystem.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness first;
  ASSERT_TRUE(first.binder.LoadLibrary(path));
  ASSERT_NE(first.binder.Bind({"top"}), nullptr);

  BindHarness second;
  ASSERT_TRUE(second.binder.LoadLibrary(path));
  auto* design = second.binder.Bind({"top"});
  ASSERT_FALSE(second.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
}

TEST(SeparateCompilationBinding, LoadingAFileThatIsNoCompiledFormIsReported) {
  // The format a compiled form is held in is this tool's own. A file it did not
  // write yields no cells, and a bind that went ahead on an empty library would
  // blame the design for what was really an unreadable library.
  ScratchDir tmp;
  auto path = tmp.Write("rtlLib.dpl", "this file was written by someone else");

  BindHarness h;
  EXPECT_FALSE(h.binder.LoadLibrary(path));
  // A library that cannot be read is a fact about the run, so this report too
  // stands at no position and enforces no subclause.
  EXPECT_TRUE(
      ReportedError(h.diag.Diagnostics(), "no cells read from library", 0, ""));
}

// §33.5.3: "The only restriction is that all cells in a design shall be
// precompiled prior to binding the design." The report naming a cell no loaded
// library holds carries that subclause, which lets a caller learn which rule
// stopped the bind without matching the wording of the message.
TEST(SeparateCompilationBinding, CellNotPrecompiledNames33_5_3) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kTwoMissing, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"two_missing"}), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cell 'gone_a' was not precompiled", 2, "33.5.3"));
}

// §33.5.3: the report naming a cell no loaded library holds stands at the
// instantiation that named it. The instantiation is the only place the design
// asks for that cell, so a report standing anywhere else tells somebody whose
// bind was refused what is missing and not which instance wanted it -- and a
// design short of several cells produces sentences with nothing to tell them
// apart. The binder reports through the source manager the library was read
// into, so the position of an instantiation inside a precompiled cell resolves.
TEST(SeparateCompilationBinding, CellNotPrecompiledStandsAtItsInstantiation) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMissingBelowAnother, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"missing_below_another"}), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cell 'gone' was not precompiled", 4, "33.5.3"));
}

// A source description whose compilation-unit scope holds a typedef beside the
// cell it declares. §3.12.1 is what makes the two travel differently.
constexpr const char* kLeafBesideACuTypedef =
    "typedef logic [7:0] byte_t;\n"
    "module leaf;\n"
    "endmodule\n";

// ---------------------------------------------------------------------------
// Claim: a cell reaches a later run through its precompiled form, and the
// compilation-unit scope it was compiled beside does not.
// ---------------------------------------------------------------------------

TEST(SeparateCompilationBinding,
     CompilationUnitDeclarationDoesNotCrossAPrecompiledRecord) {
  // §3.12.1 case b): "each file is a separate compilation unit (in which case
  // the declarations in each compilation-unit scope are accessible only within
  // its corresponding file)". A precompiled record was written by a compiler
  // invocation of its own, so the unit it is read into is not the unit it was
  // compiled in, and the typedef the description wrote outside every design
  // element stays behind. The cell does cross, which is the whole point of
  // precompiling it.
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeafBesideACuTypedef, "rtlLib", path);

  BindHarness h;
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, h.mgr, h.arena, h.diag));
  ASSERT_EQ(target.modules.size(), 1u);
  EXPECT_EQ(target.modules[0]->name, "leaf");
  EXPECT_TRUE(target.cu_items.empty());
}

}  // namespace
