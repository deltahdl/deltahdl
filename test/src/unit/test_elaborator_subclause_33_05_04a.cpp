#include <gtest/gtest.h>

#include <filesystem>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/command_line_bind.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/library_map.h"
#include "parser/precompiled_library.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct CommandLineHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
  std::optional<Elaborator> elab;

  RtlirDesign* Run(const fs::path& dir, const std::vector<fs::path>& line,
                   std::string_view top = "", std::string_view config = "") {
    if (!libs.LoadMapFile(dir / "lib.map")) return nullptr;
    if (!compiler.CompileCommandLine(line, unit)) return nullptr;
    if (diag.HasErrors()) return nullptr;
    elab.emplace(arena, diag, &unit);
    return ElaborateCommandLine(*elab, unit, top, config, diag);
  }
};

std::string_view LibraryOfTheOnlyChild(const RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return {};
  const auto& children = design->top_modules[0]->children;
  if (children.size() != 1u || children[0].resolved == nullptr) return {};
  return children[0].resolved->library;
}

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
  s.gate_top = tmp.Write("gate/top.v",
                         "module top;\n"
                         "endmodule\n");
  return s;
}

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

RtlirDesign* RunDelegation(ScratchDir& tmp, CommandLineHarness& h,
                           const std::string& outer_config) {
  auto s = WriteDelegationSources(tmp);
  auto outer = tmp.Write("src/cfg_top.v", outer_config);
  return h.Run(tmp.dir, {s.child, s.alt, s.top, outer, s.inner});
}

std::vector<std::string_view> NamesBoundUnderTheRoot(RtlirDesign* design) {
  auto* top = design == nullptr || design->top_modules.size() != 1u
                  ? nullptr
                  : design->top_modules[0];
  if (top == nullptr) return {};
  std::vector<std::string_view> names;
  names.reserve(top->children.size());
  for (const auto& child : top->children) {
    names.emplace_back(child.resolved == nullptr ? "" : child.resolved->name);
  }
  return names;
}

struct TwoConfigSources {
  fs::path child;
  fs::path top;
  fs::path other;
  fs::path cfg_top;
  fs::path cfg_other;
};

TwoConfigSources WriteTwoConfigSources(ScratchDir& tmp) {
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  TwoConfigSources s;
  s.child = tmp.Write("src/child.v",
                      "module child;\n"
                      "endmodule\n");
  s.top = tmp.Write("src/top.v",
                    "module top;\n"
                    "  child c();\n"
                    "endmodule\n");
  s.other = tmp.Write("src/other.v",
                      "module other;\n"
                      "  child o();\n"
                      "endmodule\n");
  s.cfg_top = tmp.Write("src/cfg_top.v",
                        "config cfg_top;\n"
                        "  design top;\n"
                        "endconfig\n");
  s.cfg_other = tmp.Write("src/cfg_other.v",
                          "config cfg_other;\n"
                          "  design other;\n"
                          "endconfig\n");
  return s;
}

std::vector<fs::path> TwoConfigCommandLine(const TwoConfigSources& s) {
  return {s.child, s.top, s.other, s.cfg_top, s.cfg_other};
}

TEST(CommandLineBinding, DesignStatementOfTheNamedConfigRootsTheDesignAlone) {
  ScratchDir tmp;
  auto s = WriteSources(tmp);

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, {s.child, s.spare, s.top, s.cfg});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_TRUE(design->all_modules.contains("child"));
  EXPECT_FALSE(design->all_modules.contains("spare"));
}

TEST(CommandLineBinding, ConfigHeldInTheLibraryOffThisCommandLineIsNotInForce) {
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
  auto* design = ElaborateCommandLine(elab, h.unit, "", "", h.diag);
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "spare");
}

TEST(CommandLineBinding, DesignStatementOutranksTheTopNamedOnTheCommandLine) {
  ScratchDir tmp;
  auto s = WriteSources(tmp);

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, {s.child, s.spare, s.top, s.cfg}, "spare");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(CommandLineBinding, TopNamedOnTheCommandLineRootsADesignWithNoConfig) {
  ScratchDir tmp;
  auto s = WriteSources(tmp);

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, {s.child, s.top, s.spare}, "spare");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "spare");
}

TEST(CommandLineBinding, ConfigDelegatedToDoesNotRootADesignOfItsOwn) {
  ScratchDir tmp;
  CommandLineHarness h;
  auto* design = RunDelegation(tmp, h,
                               "config cfg_top;\n"
                               "  design top;\n"
                               "  default liblist rtlLib;\n"
                               "  instance top.c use cfg_child:config;\n"
                               "  instance top.d use rtlLib.alt;\n"
                               "endconfig\n");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(NamesBoundUnderTheRoot(design),
            (std::vector<std::string_view>{"alt", "alt"}));
}

TEST(CommandLineBinding, ConfigDelegatedToByBareNameDoesNotRootADesign) {
  ScratchDir tmp;
  CommandLineHarness h;
  auto* design = RunDelegation(tmp, h,
                               "config cfg_top;\n"
                               "  design top;\n"
                               "  instance top.c use cfg_child;\n"
                               "endconfig\n");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(NamesBoundUnderTheRoot(design),
            (std::vector<std::string_view>{"alt", "child"}));
}

TEST(CommandLineBinding, EveryCellTheDesignStatementNamesRootsTheDesign) {
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
  auto* design = h.Run(tmp.dir, {s.child, s.top, other, s.spare, two});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "other");
  EXPECT_FALSE(design->all_modules.contains("spare"));
}

TEST(CommandLineBinding, LibraryQualifyingTheDesignCellPicksWhichCellRoots) {
  ScratchDir tmp;
  auto s = WriteTwoLibrarySources(tmp);
  auto cfg = tmp.Write("rtl/cfg.v",
                       "config cfg;\n"
                       "  design gateLib.top;\n"
                       "endconfig\n");

  CommandLineHarness h;
  auto* design =
      h.Run(tmp.dir, {s.rtl_child, s.gate_child, s.rtl_top, s.gate_top, cfg});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[0]->library, "gateLib");
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(CommandLineBinding, QualifiedDesignCellAbsentFromThatLibraryIsReported) {
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
  auto* design = h.Run(
      tmp.dir, {s.rtl_child, s.gate_child, s.rtl_top, s.gate_top, only, cfg});
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(),
      "config 'cfg' design cell 'rtl_only' not found in library 'gateLib'", 2,
      "33.4.1.1"));
}

TEST(CommandLineBinding, ConfigNamingNoCellAtAllPutsNoDesignInForce) {
  ScratchDir tmp;
  auto s = WriteSources(tmp);
  auto empty = tmp.Write("src/cfg_empty.v",
                         "config cfg_empty;\n"
                         "  design;\n"
                         "endconfig\n");

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, {s.child, s.top, s.spare, empty});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "spare");
}

TEST(CommandLineBinding, TwoConfigsNamingDesignsOfTheirOwnAreReported) {
  ScratchDir tmp;
  auto s = WriteSources(tmp);
  auto other = tmp.Write("src/cfg_spare.v",
                         "config cfg_spare;\n"
                         "  design spare;\n"
                         "endconfig\n");

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, {s.child, s.spare, s.top, s.cfg, other});
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "command line puts 2 configurations in force; "
                            "'cfg' and 'cfg_spare' each name a design of their "
                            "own",
                            0, "33.5.4"));
}

TEST(CommandLineBinding, NamedConfigPicksItsOwnDesignFromTwoInForce) {
  ScratchDir tmp;
  auto s = WriteTwoConfigSources(tmp);

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, TwoConfigCommandLine(s), "", "cfg_top");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_FALSE(design->all_modules.contains("other"));
}

TEST(CommandLineBinding, NamingTheOtherConfigInForcePicksTheOtherDesign) {
  ScratchDir tmp;
  auto s = WriteTwoConfigSources(tmp);

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, TwoConfigCommandLine(s), "", "cfg_other");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "other");
  EXPECT_FALSE(design->all_modules.contains("top"));
}

TEST(CommandLineBinding, TwoConfigsInForceAreStillReportedWithNoConfigNamed) {
  ScratchDir tmp;
  auto s = WriteTwoConfigSources(tmp);

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, TwoConfigCommandLine(s));
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "command line puts 2 configurations in force", 0,
                            "33.5.4"));
}

TEST(CommandLineBinding, ConfigNameMatchingNothingInTheUnitIsReported) {
  ScratchDir tmp;
  auto s = WriteTwoConfigSources(tmp);

  CommandLineHarness h;
  auto* design = h.Run(tmp.dir, TwoConfigCommandLine(s), "", "cfg_absent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(),
      "no configuration named 'cfg_absent' is in force; the command line put 2 "
      "in force",
      0, "33.5.4"));
}

TEST(CommandLineBinding, ConfigNamingNoDesignIsNotSelectableByName) {
  ScratchDir tmp;
  auto s = WriteSources(tmp);
  auto empty = tmp.Write("src/cfg_empty.v",
                         "config cfg_empty;\n"
                         "  design;\n"
                         "endconfig\n");

  CommandLineHarness h;
  auto* design =
      h.Run(tmp.dir, {s.child, s.top, s.spare, s.cfg, empty}, "", "cfg_empty");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(),
      "no configuration named 'cfg_empty' is in force; the command line put 1 "
      "in force",
      0, "33.5.4"));
}

TEST(CommandLineBinding, DefaultClauseOfTheConfigInForceBindsTheInstances) {
  ScratchDir tmp;
  auto s = WriteTwoLibrarySources(tmp);
  auto cfg = tmp.Write("rtl/cfg.v",
                       "config cfg;\n"
                       "  design rtlLib.top;\n"
                       "  default liblist gateLib;\n"
                       "endconfig\n");

  CommandLineHarness h;
  auto* design =
      h.Run(tmp.dir, {s.rtl_child, s.gate_child, s.rtl_top, s.gate_top, cfg});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(LibraryOfTheOnlyChild(design), "gateLib");
}

TEST(CommandLineBinding, CellClauseOfTheConfigInForceBindsTheInstances) {
  ScratchDir tmp;
  auto s = WriteTwoLibrarySources(tmp);
  auto cfg = tmp.Write("rtl/cfg.v",
                       "config cfg;\n"
                       "  design rtlLib.top;\n"
                       "  cell child liblist gateLib;\n"
                       "endconfig\n");

  CommandLineHarness h;
  auto* design =
      h.Run(tmp.dir, {s.rtl_child, s.gate_child, s.rtl_top, s.gate_top, cfg});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(LibraryOfTheOnlyChild(design), "gateLib");
}

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

constexpr const char* kSpareConfig =
    "config cfg_spare;\n"
    "  design spare;\n"
    "endconfig\n";
constexpr const char* kEmptyConfig =
    "config cfg_empty;\n"
    "  design;\n"
    "endconfig\n";

constexpr const char* kGateTop =
    "module top;\n"
    "endmodule\n";
constexpr const char* kQualifiedConfig =
    "config cfg_gate;\n"
    "  design gateLib.top;\n"
    "endconfig\n";

TEST(ConfigDrivenBinding, ConfigNameAloneDescribesTheWholeDesign) {
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
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kTop, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kChild, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kEmptyConfig, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg_empty");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "config 'cfg_empty' names no design", 1,
                            "33.4.1.1"));
}

TEST(ConfigDrivenBinding, ConfigNoCompiledFormHoldsIsReported) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kChild, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kTop, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "config 'cfg' was not precompiled", 0, "33.5.4"));
}

TEST(ConfigDrivenBinding, CellTheDesignStatementNamesMustBePrecompiledToo) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(kChild, "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(kConfig, "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.BindConfig("cfg");
  EXPECT_EQ(design, nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 1u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0].name, "top");
}

TEST(ConfigDrivenBinding, DesignStatementLibraryPicksWhichPrecompiledCell) {
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
