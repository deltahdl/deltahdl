#include <gtest/gtest.h>

#include <cstddef>
#include <filesystem>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_scratch_dir.h"
#include "lexer/lexer.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

constexpr const char* kExampleMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib adder.vg;\n";

constexpr const char* kDollarNameMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gate$Lib2 adder.vg;\n";

constexpr const char* kTopFile =
    "module top;\n"
    "  adder a1();\n"
    "  m u1();\n"
    "endmodule\n";

constexpr const char* kAdderRtlFile =
    "module adder;\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kAdderGateFile =
    "module adder;\n"
    "endmodule\n";

constexpr const char* kConfigFile =
    "config cfg;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib;\n"
    "endconfig\n";

constexpr const char* kNoDefaultConfigFile =
    "config cfg;\n"
    "  design rtlLib.top;\n"
    "endconfig\n";

constexpr const char* kTopLibraryAdderMap =
    "library rtlLib top.v, rtladder.v;\n"
    "library aLib adder.*;\n"
    "library gateLib adder.vg;\n";

constexpr const char* kUnderscoreNameMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library _gate_lib adder.vg;\n";

constexpr const char* kSubdirectoryMap =
    "library rtlLib top.v;\n"
    "library dirLib sub/;\n"
    "library fileLib sub/adder.vg;\n";

constexpr const char* kWidgetMap =
    "library rtlLib top.v;\n"
    "library aLib w.v;\n"
    "library gateLib w.vg;\n";

constexpr const char* kWidgetPrimitiveFirstMap =
    "library rtlLib top.v;\n"
    "library gateLib w.vg;\n"
    "library aLib w.v;\n";

constexpr const char* kWidgetModule =
    "module w(output y, input a);\n"
    "  assign y = ~a;\n"
    "endmodule\n";
constexpr const char* kWidgetPrimitive =
    "primitive w(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";
constexpr const char* kWidgetTop =
    "module top;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w u(y, a);\n"
    "endmodule\n";

struct SourceFile {
  std::string name;
  std::string text;
};

struct LibraryDesign {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap map;
  CompilationUnit* unit = nullptr;
};

template <typename T>
void CarryAcross(std::vector<T>& into, const std::vector<T>& from) {
  into.insert(into.end(), from.begin(), from.end());
}

void MergeUnit(LibraryDesign& d, CompilationUnit* cu) {
  if (d.unit == nullptr) {
    d.unit = cu;
    return;
  }
  CarryAcross(d.unit->modules, cu->modules);
  CarryAcross(d.unit->interfaces, cu->interfaces);
  CarryAcross(d.unit->programs, cu->programs);
  CarryAcross(d.unit->checkers, cu->checkers);
  CarryAcross(d.unit->udps, cu->udps);
  CarryAcross(d.unit->configs, cu->configs);
}

bool Assemble(ScratchDir& tmp, LibraryDesign& d, const std::string& map_text,
              const std::vector<SourceFile>& files) {
  auto map_path = tmp.Write("lib.map", map_text);
  std::vector<fs::path> paths;
  paths.reserve(files.size());
  for (const auto& file : files) {
    paths.push_back(tmp.Write(file.name, file.text));
  }
  if (!d.map.LoadMapFile(map_path)) return false;

  for (size_t i = 0; i < files.size(); ++i) {
    auto fid = d.mgr.AddFile(paths[i].string(), files[i].text);
    Lexer lexer(d.mgr.FileContent(fid), fid, d.diag);
    Parser parser(lexer, d.arena, d.diag);
    auto* cu = parser.Parse();
    if (cu == nullptr || d.diag.HasErrors()) return false;
    d.map.TagCompilationUnit(*cu, paths[i].string());
    MergeUnit(d, cu);
  }
  return d.unit != nullptr;
}

std::vector<SourceFile> DesignFiles() {
  std::vector<SourceFile> files;
  files.push_back({"adder.vg", kAdderGateFile});
  files.push_back({"adder.v", kAdderRtlFile});
  files.push_back({"top.v", kTopFile});
  return files;
}

bool BuildDesign(ScratchDir& tmp, LibraryDesign& d,
                 const std::string& map_text) {
  return Assemble(tmp, d, map_text, DesignFiles());
}

bool BuildConfiguredDesign(ScratchDir& tmp, LibraryDesign& d) {
  auto files = DesignFiles();
  files.push_back({"cfg.sv", kConfigFile});
  return Assemble(tmp, d, kExampleMap, files);
}

std::vector<SourceFile> WidgetFiles() {
  std::vector<SourceFile> files;
  files.push_back({"w.vg", kWidgetPrimitive});
  files.push_back({"w.v", kWidgetModule});
  files.push_back({"top.v", kWidgetTop});
  return files;
}

struct CellKindFixture {
  std::string base;
  std::string cell;
  std::string top;
};

bool BuildCellKindDesign(ScratchDir& tmp, LibraryDesign& d,
                         const CellKindFixture& c) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library aLib " + c.base + ".v;\n";
  map_text += "library gateLib " + c.base + ".vg;\n";
  std::vector<SourceFile> files;
  files.push_back({c.base + ".vg", c.cell});
  files.push_back({c.base + ".v", c.cell});
  files.push_back({"top.v", c.top});
  return Assemble(tmp, d, map_text, files);
}

RtlirDesign* ElaborateWithOrder(LibraryDesign& d, std::string_view top,
                                std::vector<std::string> order) {
  Elaborator elab(d.arena, d.diag, d.unit);
  elab.SetLibraryDeclarationOrder(std::move(order));
  return elab.Elaborate(top);
}

RtlirDesign* ElaborateConfigWithOrder(LibraryDesign& d,
                                      std::vector<std::string> order) {
  Elaborator elab(d.arena, d.diag, d.unit);
  elab.SetLibraryDeclarationOrder(std::move(order));
  return elab.Elaborate(d.unit->configs.front());
}

RtlirModule* SoleTopOf(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return nullptr;
  return design->top_modules[0];
}

RtlirModule* BoundCell(RtlirDesign* design, std::string_view inst) {
  auto* top = SoleTopOf(design);
  if (top == nullptr) return nullptr;
  for (const auto& child : top->children) {
    if (child.inst_name == inst) return child.resolved;
  }
  return nullptr;
}

std::string_view BoundLibrary(RtlirDesign* design, std::string_view inst) {
  auto* cell = BoundCell(design, inst);
  return cell == nullptr ? std::string_view{} : cell->library;
}

std::string Joined(const std::vector<std::string>& order) {
  std::string out;
  for (const auto& name : order) {
    if (!out.empty()) out += ' ';
    out += name;
  }
  return out;
}

template <typename Decls>
bool AnyDeclIn(const Decls& decls, std::string_view cell,
               std::string_view library) {
  for (const auto* decl : decls) {
    if (decl->name == cell && decl->library == library) return true;
  }
  return false;
}

bool UnitHoldsCellIn(const CompilationUnit* unit, std::string_view cell,
                     std::string_view library) {
  return AnyDeclIn(unit->modules, cell, library) ||
         AnyDeclIn(unit->interfaces, cell, library) ||
         AnyDeclIn(unit->programs, cell, library) ||
         AnyDeclIn(unit->checkers, cell, library) ||
         AnyDeclIn(unit->udps, cell, library);
}

TEST(CommandLineLibrarySearchOrder,
     NoCommandLineOrderLeavesTheMapDeclarationOrderStanding) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "gateLib"));

  auto order = d.map.ResolveSearchOrder({});
  EXPECT_EQ(Joined(order), "rtlLib aLib gateLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "aLib");
}

TEST(CommandLineLibrarySearchOrder,
     CommandLineOrderReplacesTheMapDeclarationOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "aLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib", "aLib", "rtlLib"});
  EXPECT_EQ(Joined(order), "gateLib aLib rtlLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

TEST(CommandLineLibrarySearchOrder,
     LibraryLeftOffTheCommandLineOrderIsStillSearched) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "m", "aLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  auto* design = ElaborateWithOrder(d, "top", order);
  EXPECT_EQ(BoundLibrary(design, "a1"), "gateLib");
  EXPECT_EQ(BoundLibrary(design, "u1"), "aLib");
}

TEST(CommandLineLibrarySearchOrder,
     UnnamedLibrariesKeepTheirDeclaredOrderBehindTheNamedOnes) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "gateLib"));
  ASSERT_FALSE(UnitHoldsCellIn(d.unit, "adder", "rtlLib"));

  auto order = d.map.ResolveSearchOrder({"rtlLib"});
  EXPECT_EQ(Joined(order), "rtlLib aLib gateLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "aLib");
}

TEST(CommandLineLibrarySearchOrder,
     CommandLineNameNoDeclarationIntroducedRanksAnEmptyLibrary) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  EXPECT_FALSE(UnitHoldsCellIn(d.unit, "adder", "phantomLib"));

  auto order = d.map.ResolveSearchOrder({"phantomLib", "gateLib", "aLib"});
  EXPECT_EQ(Joined(order), "phantomLib gateLib aLib rtlLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

TEST(CommandLineLibrarySearchOrder,
     LibraryNamedTwiceOnTheCommandLineIsRankedOnce) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));

  auto order = d.map.ResolveSearchOrder({"gateLib", "aLib", "gateLib"});
  EXPECT_EQ(Joined(order), "gateLib aLib rtlLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

TEST(CommandLineLibrarySearchOrder,
     CommandLineEntryNamingAFileIsNotALibraryName) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));

  std::vector<std::string> errors;
  auto order = d.map.ResolveSearchOrder({"adder.vg", "gateLib"}, &errors);
  ASSERT_EQ(errors.size(), 1u);
  EXPECT_NE(errors[0].find("adder.vg"), std::string::npos);
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

TEST(CommandLineLibrarySearchOrder, NoEntryButALibraryNameEntersTheOrder) {
  std::vector<std::string> entries;
  entries.push_back("/proj/lib1/*.v");
  entries.push_back("*.v");
  entries.push_back("2lib");
  entries.push_back("");
  entries.push_back("a-lib");

  LibraryMap map;
  std::vector<std::string> errors;
  auto order = map.ResolveSearchOrder(entries, &errors);
  EXPECT_TRUE(order.empty());
  EXPECT_EQ(errors.size(), entries.size());
}

TEST(CommandLineLibrarySearchOrder,
     LibraryNameWithDigitAndDollarSignIsALibraryName) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kDollarNameMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "gate$Lib2"));

  std::vector<std::string> errors;
  auto order = d.map.ResolveSearchOrder({"gate$Lib2"}, &errors);
  EXPECT_TRUE(errors.empty());
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"),
            "gate$Lib2");
}

TEST(CommandLineLibrarySearchOrder,
     ConfigurationInForceSettlesWhatTheCommandLineOrderWould) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildConfiguredDesign(tmp, d));
  ASSERT_FALSE(d.unit->configs.empty());

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  EXPECT_EQ(BoundLibrary(ElaborateConfigWithOrder(d, order), "a1"), "aLib");
}

TEST(CommandLineLibrarySearchOrder,
     ConfigurationWithNoDefaultClauseOverridesTheCommandLineOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  auto files = DesignFiles();
  files.push_back({"rtladder.v", kAdderGateFile});
  files.push_back({"cfg.sv", kNoDefaultConfigFile});
  ASSERT_TRUE(Assemble(tmp, d, kTopLibraryAdderMap, files));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "rtlLib"));
  ASSERT_FALSE(d.unit->configs.empty());

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  EXPECT_EQ(BoundLibrary(ElaborateConfigWithOrder(d, order), "a1"), "rtlLib");
}

TEST(CommandLineLibrarySearchOrder,
     LibraryNameOpeningWithAnUnderscoreIsALibraryName) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kUnderscoreNameMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "_gate_lib"));

  std::vector<std::string> errors;
  auto order = d.map.ResolveSearchOrder({"_gate_lib"}, &errors);
  EXPECT_TRUE(errors.empty());
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"),
            "_gate_lib");
}

TEST(CommandLineLibrarySearchOrder,
     CellPlacedByTheDirectoryTierIsRankedByTheCommandLine) {
  ScratchDir tmp;
  LibraryDesign d;
  std::vector<SourceFile> files;
  files.push_back({"sub/adder.vg", kAdderGateFile});
  files.push_back({"sub/adder.v", kAdderRtlFile});
  files.push_back({"top.v", kTopFile});
  ASSERT_TRUE(Assemble(tmp, d, kSubdirectoryMap, files));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "fileLib"));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "dirLib"));

  auto order = d.map.ResolveSearchOrder({"fileLib", "dirLib"});
  EXPECT_EQ(Joined(order), "fileLib dirLib rtlLib");
  auto* design = ElaborateWithOrder(d, "top", order);
  EXPECT_EQ(BoundLibrary(design, "a1"), "fileLib");
  EXPECT_EQ(BoundLibrary(design, "u1"), "dirLib");
}

TEST(CommandLineLibrarySearchOrder,
     InterfaceCellIsRankedByTheCommandLineOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  CellKindFixture c;
  c.base = "bus";
  c.cell = "interface bus;\nendinterface\n";
  c.top = "module top;\n  bus b();\nendmodule\n";
  ASSERT_TRUE(BuildCellKindDesign(tmp, d, c));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "bus", "aLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  auto* bound = BoundCell(ElaborateWithOrder(d, "top", order), "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(CommandLineLibrarySearchOrder,
     PrimitiveCellIsRankedByTheCommandLineOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(Assemble(tmp, d, kWidgetMap, WidgetFiles()));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "w", "aLib"));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "w", "gateLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  auto* top = SoleTopOf(ElaborateWithOrder(d, "top", order));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->children.empty());
}

TEST(CommandLineLibrarySearchOrder,
     CommandLineOrderCanGiveTheNameBackToTheModule) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(Assemble(tmp, d, kWidgetPrimitiveFirstMap, WidgetFiles()));
  ASSERT_EQ(Joined(d.map.ResolveSearchOrder({})), "rtlLib gateLib aLib");

  auto order = d.map.ResolveSearchOrder({"aLib"});
  EXPECT_EQ(Joined(order), "aLib rtlLib gateLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "u"), "aLib");
}

}  // namespace
