#include <gtest/gtest.h>

#include <filesystem>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/command_line_bind.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/precompiled_library.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// §33.5.4 is about what a command line settles. In the use models where source
// descriptions are named on it, a configuration is put in force by naming its
// own source description among them, and the design statement that
// configuration carries then names the top-level module -- whatever cells the
// rest of the named descriptions declare and leave uninstantiated. Where a
// separate compilation tool did the compiling, the tool that binds is given the
// name of the configuration instead of the names of the top-level cells, and
// the configuration itself has to have been precompiled for that to be
// possible.
//
// These tests build their input the way the clause describes it: source
// descriptions on disk, mapped to libraries by a §33.3.1 library map and
// compiled by §33.5.1's single-pass compiler, or written into a compiled form
// and read back by §33.5.3's binder. What the rules turn on is precisely which
// descriptions a command line named, so a compilation unit assembled by a test
// would settle nothing.

// The infrastructure one command line is compiled and elaborated against.
struct CommandLineHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

// The source descriptions a command line may name: a two-cell hierarchy, a
// cell no instance names, and a configuration whose design statement names the
// hierarchy's root. Every one of them is a file of its own, so a command line
// can name any subset of them.
struct Sources {
  fs::path top;
  fs::path child;
  fs::path spare;
  fs::path cfg;
};

Sources WriteSources(ScratchDir& tmp) {
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  Sources s;
  s.child = tmp.Write("src/child.v",
                      "module child;\n"
                      "endmodule\n");
  s.top = tmp.Write("src/top.v",
                    "module top;\n"
                    "  child c();\n"
                    "endmodule\n");
  s.spare = tmp.Write("src/spare.v",
                      "module spare;\n"
                      "endmodule\n");
  s.cfg = tmp.Write("src/cfg.v",
                    "config cfg;\n"
                    "  design top;\n"
                    "endconfig\n");
  return s;
}

// A command line whose descriptions come from two libraries, each holding a
// cell of the name the other holds too. Which library a name is taken from is
// then something the run has to settle, so a rule that settles it is visible in
// the design it produces. The configuration's own description goes into rtlLib.
struct TwoLibrarySources {
  fs::path rtl_top;
  fs::path rtl_child;
  fs::path gate_top;
  fs::path gate_child;
};

TwoLibrarySources WriteTwoLibrarySources(ScratchDir& tmp) {
  tmp.Write("lib.map",
            "library rtlLib rtl/*.v;\n"
            "library gateLib gate/*.v;\n");
  TwoLibrarySources s;
  s.rtl_child = tmp.Write("rtl/child.v",
                          "module child;\n"
                          "endmodule\n");
  s.gate_child = tmp.Write("gate/child.v",
                           "module child;\n"
                           "endmodule\n");
  s.rtl_top = tmp.Write("rtl/top.v",
                        "module top;\n"
                        "  child c();\n"
                        "endmodule\n");
  // The gate-level root instantiates nothing, so which of the two roots a
  // design is legible from the design alone.
  s.gate_top = tmp.Write("gate/top.v",
                         "module top;\n"
                         "endmodule\n");
  return s;
}

// The descriptions a delegating configuration works over: a root with two child
// instances, the cell those instances are declared to be, the cell an inner
// configuration puts in that cell's place, and the inner configuration itself.
struct DelegationSources {
  fs::path child;
  fs::path alt;
  fs::path top;
  fs::path inner;
};

DelegationSources WriteDelegationSources(ScratchDir& tmp) {
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  DelegationSources s;
  s.child = tmp.Write("src/child.v",
                      "module child;\n"
                      "endmodule\n");
  s.alt = tmp.Write("src/alt.v",
                    "module alt;\n"
                    "endmodule\n");
  s.top = tmp.Write("src/top.v",
                    "module top;\n"
                    "  child c();\n"
                    "  child d();\n"
                    "endmodule\n");
  s.inner = tmp.Write("src/cfg_child.v",
                      "config cfg_child;\n"
                      "  design alt;\n"
                      "endconfig\n");
  return s;
}

// ---------------------------------------------------------------------------
// Claim: in the single-pass use models the configuration is put in force by
// naming its source description on the command line, and where that
// configuration includes a design statement the cell it names is the top-level
// module -- whatever uninstantiated cells the rest of the source files hold.
// ---------------------------------------------------------------------------

TEST(CommandLineBinding, DesignStatementOfTheNamedConfigRootsTheDesignAlone) {
  // The configuration's description is on this command line, so its design
  // statement settles the design: top roots it, and the cell top instantiates
  // is bound beneath it. spare.v is on the same command line and no instance
  // anywhere names the cell it declares, which is exactly the condition that
  // would make it a top-level module of its own. The design statement is what
  // stops it being one.
  ScratchDir tmp;
  auto s = WriteSources(tmp);

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.spare, s.top, s.cfg};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_TRUE(design->all_modules.contains("child"));
  EXPECT_FALSE(design->all_modules.contains("spare"));
}

TEST(CommandLineBinding, ConfigHeldInTheLibraryOffThisCommandLineIsNotInForce) {
  // The command line above with the configuration's description struck off it,
  // so this is also what says that the test above measures the design statement
  // rather than something about spare: spare is a top-level module here.
  //
  // cfg.v sits on disk beside the rest and an earlier command line has already
  // compiled it, so its cell is in rtlLib right now, as the test asserts before
  // elaborating. What puts a configuration in force is nevertheless this
  // command line naming its source description, and this one does not: the
  // uninstantiated cell roots a design of its own again. Leaving cfg.v out of
  // the library altogether would prove less, because a tool that consulted the
  // library instead of the command line would pass that case too.
  ScratchDir tmp;
  auto s = WriteSources(tmp);

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  CompilationUnit earlier;
  ASSERT_TRUE(h.compiler.CompileCommandLine({s.cfg}, earlier));
  ASSERT_NE(h.libs.CellInLibrary("rtlLib", "cfg"), nullptr);

  std::vector<fs::path> line{s.child, s.top, s.spare};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "spare");
}

TEST(CommandLineBinding, DesignStatementOutranksTheTopNamedOnTheCommandLine) {
  // A command line may name a top-level cell as well. The design statement is
  // what says which cell is the top-level module, so naming spare alongside the
  // configuration does not make spare root the design.
  ScratchDir tmp;
  auto s = WriteSources(tmp);

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.spare, s.top, s.cfg};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "spare", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(CommandLineBinding, TopNamedOnTheCommandLineRootsADesignWithNoConfig) {
  // The other half of the same command line: with no configuration in force the
  // named top-level cell is what the design is rooted at, and the cell no
  // instance names does not root one beside it.
  ScratchDir tmp;
  auto s = WriteSources(tmp);

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.top, s.spare};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "spare", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "spare");
}

TEST(CommandLineBinding, ConfigDelegatedToDoesNotRootADesignOfItsOwn) {
  // Two configurations reach the command line, and both carry a design
  // statement, but one of them is what the other delegates an instance to: it
  // describes a subtree of the outer design rather than a design of its own.
  // The outer configuration is the one in force, so the design is rooted at
  // top -- and top.c binds to the cell the inner configuration names, which is
  // how the delegation shows it was honoured rather than ignored.
  //
  // The outer configuration also carries the two rule shapes that are not a
  // delegation -- a default clause, and an instance clause whose use names a
  // cell outright -- so the question of which configuration was delegated to is
  // asked of a configuration that holds more than delegations.
  ScratchDir tmp;
  auto s = WriteDelegationSources(tmp);
  auto outer = tmp.Write("src/cfg_top.v",
                         "config cfg_top;\n"
                         "  design top;\n"
                         "  default liblist rtlLib;\n"
                         "  instance top.c use cfg_child:config;\n"
                         "  instance top.d use rtlLib.alt;\n"
                         "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.alt, s.top, outer, s.inner};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  ASSERT_EQ(design->top_modules[0]->children.size(), 2u);
  ASSERT_NE(design->top_modules[0]->children[0].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[0].resolved->name, "alt");
}

TEST(CommandLineBinding, ConfigDelegatedToByBareNameDoesNotRootADesign) {
  // The other way a use clause reaches a configuration: the plain name, with no
  // extension after it. It reaches the configuration because nothing else the
  // command line named answers to that name, and a configuration reached that
  // way is as much a subtree of the outer design as one reached by the
  // extension -- so it roots no design of its own here either.
  //
  // Only top.c is delegated. top.d keeps the cell its instantiation declares,
  // which is what shows the delegation reached the one instance it named rather
  // than everything below the root.
  ScratchDir tmp;
  auto s = WriteDelegationSources(tmp);
  auto outer = tmp.Write("src/cfg_top.v",
                         "config cfg_top;\n"
                         "  design top;\n"
                         "  instance top.c use cfg_child;\n"
                         "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.alt, s.top, outer, s.inner};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  ASSERT_EQ(design->top_modules[0]->children.size(), 2u);
  ASSERT_NE(design->top_modules[0]->children[0].resolved, nullptr);
  ASSERT_NE(design->top_modules[0]->children[1].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[0].resolved->name, "alt");
  EXPECT_EQ(design->top_modules[0]->children[1].resolved->name, "child");
}

TEST(CommandLineBinding, EveryCellTheDesignStatementNamesRootsTheDesign) {
  // A design statement names zero or more cells, so the rule that its cell is
  // the top-level module has to hold of each of them at once. Two of the three
  // uninstantiated cells on this command line are named by it and root the
  // design; the third is named by nothing and roots nothing, which is the whole
  // of what the rule adds to the cells-no-instance-names default.
  ScratchDir tmp;
  auto s = WriteSources(tmp);
  auto other = tmp.Write("src/other.v",
                         "module other;\n"
                         "  child o();\n"
                         "endmodule\n");
  auto two = tmp.Write("src/cfg_two.v",
                       "config cfg_two;\n"
                       "  design top other;\n"
                       "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.top, other, s.spare, two};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "other");
  EXPECT_FALSE(design->all_modules.contains("spare"));
}

TEST(CommandLineBinding, LibraryQualifyingTheDesignCellPicksWhichCellRoots) {
  // The other shape a design statement's cell takes: a library name in front of
  // it. Two libraries on this command line each hold a cell called top, so the
  // bare name would settle nothing; the qualified one settles it, and what
  // comes out is the gate-level root, which instantiates nothing.
  ScratchDir tmp;
  auto s = WriteTwoLibrarySources(tmp);
  auto cfg = tmp.Write("rtl/cfg.v",
                       "config cfg;\n"
                       "  design gateLib.top;\n"
                       "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.rtl_child, s.gate_child, s.rtl_top, s.gate_top,
                             cfg};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[0]->library, "gateLib");
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(CommandLineBinding, QualifiedDesignCellAbsentFromThatLibraryIsReported) {
  // The negative of the qualified shape. The cell exists and the command line
  // compiled it, but into the other library, and the qualification says which
  // library the root comes from -- so there is no root and the run is reported
  // rather than falling back on the like-named cell that is there.
  ScratchDir tmp;
  auto s = WriteTwoLibrarySources(tmp);
  auto only = tmp.Write("rtl/rtl_only.v",
                        "module rtl_only;\n"
                        "endmodule\n");
  auto cfg = tmp.Write("rtl/cfg.v",
                       "config cfg;\n"
                       "  design gateLib.rtl_only;\n"
                       "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.rtl_child, s.gate_child, s.rtl_top,
                             s.gate_top,  only,         cfg};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(h.diag.HasErrors());
}

TEST(CommandLineBinding, ConfigNamingNoCellAtAllPutsNoDesignInForce) {
  // A design statement names zero or more cells, so one that names none is
  // written legally. It puts no design in force: there is no cell for the rule
  // to make the top-level module, so the cells no instance names root the
  // design as they would have with no configuration on the command line at all.
  ScratchDir tmp;
  auto s = WriteSources(tmp);
  auto empty = tmp.Write("src/cfg_empty.v",
                         "config cfg_empty;\n"
                         "  design;\n"
                         "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.top, s.spare, empty};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "spare");
}

TEST(CommandLineBinding, TwoConfigsNamingDesignsOfTheirOwnAreReported) {
  // Neither configuration delegates to the other, so each names a whole design
  // and the command line describes two. Nothing in the source descriptions says
  // which was meant, so the command line is reported rather than one of the two
  // being picked.
  ScratchDir tmp;
  auto s = WriteSources(tmp);
  auto other = tmp.Write("src/cfg_spare.v",
                         "config cfg_spare;\n"
                         "  design spare;\n"
                         "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.child, s.spare, s.top, s.cfg, other};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(h.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// Claim: the rules that bind the design's instances come either from the
// configuration or, with none in force, from the library map file's defaults.
// The tests above carry the second half, where no configuration reaches the
// command line; these two carry the first.
// ---------------------------------------------------------------------------

TEST(CommandLineBinding, DefaultClauseOfTheConfigInForceBindsTheInstances) {
  // Both libraries on this command line hold a cell called child, and the root
  // comes from rtlLib. Its instance nonetheless binds to the gate-level child,
  // which nothing but the configuration's default clause asks for -- so the
  // rules the run works under are the ones the configuration carries.
  ScratchDir tmp;
  auto s = WriteTwoLibrarySources(tmp);
  auto cfg = tmp.Write("rtl/cfg.v",
                       "config cfg;\n"
                       "  design rtlLib.top;\n"
                       "  default liblist gateLib;\n"
                       "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.rtl_child, s.gate_child, s.rtl_top, s.gate_top,
                             cfg};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  ASSERT_NE(design->top_modules[0]->children[0].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[0].resolved->library, "gateLib");
}

TEST(CommandLineBinding, CellClauseOfTheConfigInForceBindsTheInstances) {
  // The third rule shape a configuration carries, over the same two libraries:
  // a clause naming the cell rather than the instances. It reaches the run the
  // same way the default clause does, by the configuration's description being
  // on the command line.
  ScratchDir tmp;
  auto s = WriteTwoLibrarySources(tmp);
  auto cfg = tmp.Write("rtl/cfg.v",
                       "config cfg;\n"
                       "  design rtlLib.top;\n"
                       "  cell child liblist gateLib;\n"
                       "endconfig\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  std::vector<fs::path> line{s.rtl_child, s.gate_child, s.rtl_top, s.gate_top,
                             cfg};
  ASSERT_TRUE(h.compiler.CompileCommandLine(line, h.unit));
  ASSERT_FALSE(h.diag.HasErrors());

  Elaborator elab(h.arena, h.diag, &h.unit);
  auto* design = ElaborateCommandLine(elab, h.unit, "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  ASSERT_NE(design->top_modules[0]->children[0].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[0].resolved->library, "gateLib");
}

// ---------------------------------------------------------------------------
// Claim: where a separate compilation tool did the compiling, the tool that
// binds needs only the configuration to be used -- and that configuration is
// itself precompiled.
// ---------------------------------------------------------------------------

// The infrastructure one bind runs against. A fresh instance shares nothing
// with the compiles that wrote the libraries it reads.
struct ConfigBindHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  SeparateCompilationBinder binder{mgr, arena, diag};
};

constexpr const char* kChild =
    "module child;\n"
    "endmodule\n";
constexpr const char* kTop =
    "module top;\n"
    "  child c();\n"
    "endmodule\n";
constexpr const char* kSpare =
    "module spare;\n"
    "endmodule\n";
constexpr const char* kConfig =
    "config cfg;\n"
    "  design top;\n"
    "endconfig\n";

// A second configuration, over the cell the design of kConfig leaves out, and
// one whose design statement names no cell at all.
constexpr const char* kSpareConfig =
    "config cfg_spare;\n"
    "  design spare;\n"
    "endconfig\n";
constexpr const char* kEmptyConfig =
    "config cfg_empty;\n"
    "  design;\n"
    "endconfig\n";

// A gate-level root of the same name as kTop's, for a compiled form holding
// both, and a configuration whose design statement says which library its root
// is to come from. The gate-level one instantiates nothing, so which of the two
// was bound is legible from the design.
constexpr const char* kGateTop =
    "module top;\n"
    "endmodule\n";
constexpr const char* kQualifiedConfig =
    "config cfg_gate;\n"
    "  design gateLib.top;\n"
    "endconfig\n";

TEST(ConfigDrivenBinding, ConfigNameAloneDescribesTheWholeDesign) {
  // The binder is told nothing but the name of the configuration: no top-level
  // cell, and no source description at all. Everything it binds -- the
  // configuration included -- comes out of the compiled forms, and what comes
  // back is the design that name goes with. Two things compiled into the same
  // library would otherwise have got in: spare, which no instance names and
  // which a bind that went looking for uninstantiated cells would have rooted a
  // design at, and a second configuration over spare, which the name given is
  // what rules out.
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kChild, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kTop, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kSpare, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kSpareConfig, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kConfig, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_TRUE(design->all_modules.contains("child"));
  EXPECT_FALSE(design->all_modules.contains("spare"));
}

TEST(ConfigDrivenBinding, ConfigNamingNoCellDescribesNoDesignToBind) {
  // The configuration was precompiled and its design statement names no cell,
  // so it says nothing about which cells root the design. There is nothing else
  // a bind under it could fall back on -- the names of the top-level cells are
  // precisely what naming a configuration stands in for -- so it is reported.
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kTop, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kChild, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kEmptyConfig, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg_empty");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(h.diag.HasErrors());
}

TEST(ConfigDrivenBinding, ConfigNoCompiledFormHoldsIsReported) {
  // Every cell of the design was precompiled and the configuration was not. A
  // bind reads no source description, so there is nowhere else the
  // configuration could come from and the bind cannot proceed.
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kChild, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kTop, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(h.diag.HasErrors());
}

TEST(ConfigDrivenBinding, CellTheDesignStatementNamesMustBePrecompiledToo) {
  // The configuration reached the binder and the cell its design statement
  // names did not. Naming a configuration does not exempt a design from the
  // restriction that every cell of it is precompiled before the bind begins.
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kChild, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kConfig, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg");
  EXPECT_EQ(design, nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 1u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0], "top");
}

TEST(ConfigDrivenBinding, DesignStatementLibraryPicksWhichPrecompiledCell) {
  // The specification a binding tool is given for a top-level cell carries a
  // library as well as a cell name, and where the configuration stands in for
  // that specification it is the design statement that carries the library.
  // Two invocations of the compiler put a cell called top into two different
  // libraries; the design statement names one of them, and the design that
  // comes back is that library's.
  //
  // The library has to reach the check that every cell of the design was
  // precompiled, not just the binding after it. The cell rtlLib's top
  // instantiates is deliberately left uncompiled here, so a check that took the
  // library off the specification and went looking for a top by name alone
  // would walk the wrong hierarchy and report a cell this design never has.
  ScratchDir tmp;
  auto path = tmp.dir / "design.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kTop, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kGateTop, "gateLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kQualifiedConfig, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg_gate");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[0]->library, "gateLib");
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

}  // namespace
