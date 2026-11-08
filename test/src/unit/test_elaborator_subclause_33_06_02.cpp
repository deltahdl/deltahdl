#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kExampleMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

constexpr const char* kTopFile =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kTopWithCtrlFile =
    "module top;\n"
    "  adder a1();\n"
    "  ctrl c1();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n"
    "module ctrl;\n"
    "endmodule\n";

constexpr const char* kAdderFile =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kCfgRtlFirst =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kCfgGateFirst =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib aLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kCfgTopLibraryOnly =
    "config cfg3;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "endconfig\n";

constexpr const char* kCfgUnmappedFirst =
    "config cfg4;\n"
    "  design rtlLib.top;\n"
    "  default liblist unmappedLib gateLib;\n"
    "endconfig\n";

constexpr const char* kCfgCellClauseElsewhere =
    "config cfg5;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib aLib;\n"
    "  cell bus liblist aLib;\n"
    "endconfig\n";

bool BuildExampleDesign(ScratchDir& tmp, LibraryDesign& d,
                        const std::string& top_text) {
  auto map_file = tmp.Write("lib.map", kExampleMap);
  auto gate = tmp.Write("adder.vg", kAdderFile);
  auto rtl = tmp.Write("adder.v", kAdderFile);
  auto top = tmp.Write("top.v", top_text);
  if (!d.map.LoadMapFile(map_file)) return false;
  return d.AddFile(gate, kAdderFile) && d.AddFile(rtl, kAdderFile) &&
         d.AddFile(top, top_text);
}

bool AnyBoundCellFromLibrary(const RtlirModule* mod, std::string_view library) {
  if (mod->library == library) return true;
  for (const auto& child : mod->children) {
    if (child.resolved == nullptr) continue;
    if (AnyBoundCellFromLibrary(child.resolved, library)) return true;
  }
  return false;
}

TEST(ConfigDefaultClauseExample, ListedRtlLibrarySuppliesEveryAdderInstance) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "gateLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgRtlFirst));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  auto* a2 = ChildBoundTo(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a1->name, "adder");
  EXPECT_EQ(a1->library, "aLib");
  EXPECT_EQ(a2->library, "aLib");
}

TEST(ConfigDefaultClauseExample, ListOrderBindsEveryMInstanceAgainstMapOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "m", "rtlLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgRtlFirst));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  auto* a2 = ChildBoundTo(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  auto* f1 = ChildBoundTo(a1, "f1");
  auto* f2 = ChildBoundTo(a1, "f2");
  auto* g1 = ChildBoundTo(a2, "f1");
  auto* g2 = ChildBoundTo(a2, "f2");
  ASSERT_NE(f1, nullptr);
  ASSERT_NE(f2, nullptr);
  ASSERT_NE(g1, nullptr);
  ASSERT_NE(g2, nullptr);
  EXPECT_EQ(f1->name, "m");
  EXPECT_EQ(f1->library, "aLib");
  EXPECT_EQ(f2->library, "aLib");
  EXPECT_EQ(g1->library, "aLib");
  EXPECT_EQ(g2->library, "aLib");
}

TEST(ConfigDefaultClauseExample, UnlistedLibrarySuppliesNoCellInTheDesign) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "gateLib"));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "m", "gateLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgRtlFirst));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_FALSE(AnyBoundCellFromLibrary(top, "gateLib"));
}

TEST(ConfigDefaultClauseExample, GateLibraryListedFirstSuppliesTheAdder) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "aLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgGateFirst));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  auto* a2 = ChildBoundTo(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a1->library, "gateLib");
  EXPECT_EQ(a2->library, "gateLib");
}

TEST(ConfigDefaultClauseExample, GateLibraryListedFirstSuppliesNestedM) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "m", "aLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgGateFirst));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  ASSERT_NE(a1, nullptr);
  auto* f1 = ChildBoundTo(a1, "f1");
  auto* f2 = ChildBoundTo(a1, "f2");
  ASSERT_NE(f1, nullptr);
  ASSERT_NE(f2, nullptr);
  EXPECT_EQ(f1->name, "m");
  EXPECT_EQ(f1->library, "gateLib");
  EXPECT_EQ(f2->library, "gateLib");
}

TEST(ConfigDefaultClauseExample, ListedLibraryWithoutTheCellIsPassedOver) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopWithCtrlFile));
  ASSERT_FALSE(DesignHoldsCell(d.unit, "ctrl", "gateLib"));
  ASSERT_FALSE(DesignHoldsCell(d.unit, "ctrl", "aLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgGateFirst));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "rtlLib");
  auto* a1 = ChildBoundTo(top, "a1");
  auto* c1 = ChildBoundTo(top, "c1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(c1, nullptr);
  EXPECT_EQ(a1->library, "gateLib");
  EXPECT_EQ(c1->library, "rtlLib");
}

TEST(ConfigDefaultClauseExample, CellHeldOnlyByUnlistedLibrariesIsUnbound) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "aLib"));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "gateLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgTopLibraryOnly));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(ReportedError(d.diag.Diagnostics(),
                            "default library list (rtlLib) holds no cell "
                            "'adder'",
                            2, "33.4.1.5"));
  ASSERT_EQ(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].resolved, nullptr);
}

struct OneLibraryCell {
  std::string base;
  std::string cell;
  std::string top;
};

std::string DefaultClauseConfig(std::string_view liblist) {
  std::string text = "config cfg;\n  design rtlLib.top;\n  default liblist ";
  text += liblist;
  text += ";\nendconfig\n";
  return text;
}

RtlirDesign* ElaborateOneLibraryCell(ScratchDir& tmp, LibraryDesign& d,
                                     const OneLibraryCell& c,
                                     std::string_view liblist) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library gateLib " + c.base + ".vg;\n";
  auto map_file = tmp.Write("lib.map", map_text);
  auto gate = tmp.Write(c.base + ".vg", c.cell);
  auto top = tmp.Write("top.v", c.top);
  if (!d.map.LoadMapFile(map_file)) return nullptr;
  if (!d.AddFile(gate, c.cell) || !d.AddFile(top, c.top)) return nullptr;
  return ElaborateConfigText(tmp, d, DefaultClauseConfig(liblist));
}

constexpr const char* kGateOmitted = "rtlLib";
constexpr const char* kGateListed = "rtlLib gateLib";

constexpr const char* kBusCell = "interface bus;\nendinterface\n";
constexpr const char* kBusTop = "module top;\n  bus b();\nendmodule\n";

constexpr const char* kPgmCell = "program pgm;\nendprogram\n";
constexpr const char* kPgmTop = "module top;\n  pgm p();\nendmodule\n";

constexpr const char* kChkCell = "checker chk;\nendchecker\n";
constexpr const char* kChkTop = "module top;\n  chk c1();\nendmodule\n";

constexpr const char* kPrimCell =
    "primitive w(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";
constexpr const char* kPrimTop =
    "module top;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w u(y, a);\n"
    "endmodule\n";

TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAnInterface) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "bus", .cell = kBusCell, .top = kBusTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "b"), nullptr);
  EXPECT_TRUE(
      ReportedError(d.diag.Diagnostics(),
                    "unknown module 'bus': the configuration's default library "
                    "list (rtlLib) holds no cell 'bus' for instance 'top.b'",
                    2, "33.4.1.5"));
}

TEST(ConfigDefaultClauseExample, ListedLibrarySuppliesAnInterface) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "bus", .cell = kBusCell, .top = kBusTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateListed));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAProgram) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "pgm", .cell = kPgmCell, .top = kPgmTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "p"), nullptr);
  EXPECT_TRUE(
      ReportedError(d.diag.Diagnostics(),
                    "unknown module 'pgm': the configuration's default library "
                    "list (rtlLib) holds no cell 'pgm' for instance 'top.p'",
                    2, "33.4.1.5"));
}

TEST(ConfigDefaultClauseExample, ListedLibrarySuppliesAProgram) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "pgm", .cell = kPgmCell, .top = kPgmTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateListed));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "p");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAChecker) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "chk", .cell = kChkCell, .top = kChkTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "c1"), nullptr);
  EXPECT_TRUE(
      ReportedError(d.diag.Diagnostics(),
                    "unknown module 'chk': the configuration's default library "
                    "list (rtlLib) holds no cell 'chk' for instance 'top.c1'",
                    2, "33.4.1.5"));
}

TEST(ConfigDefaultClauseExample, ListedLibrarySuppliesAChecker) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "chk", .cell = kChkCell, .top = kChkTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateListed));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "c1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAPrimitive) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "w", .cell = kPrimCell, .top = kPrimTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "w", "gateLib"));
  EXPECT_TRUE(ReportedError(d.diag.Diagnostics(),
                            "default library list (rtlLib) holds no cell 'w'",
                            4, "33.4.1.5"));
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

TEST(ConfigDefaultClauseExample, ListedLibrarySuppliesAPrimitive) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "w", .cell = kPrimCell, .top = kPrimTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateListed));
  ASSERT_NE(top, nullptr);
  EXPECT_FALSE(d.diag.HasErrors());
  EXPECT_TRUE(top->children.empty());
}

TEST(ConfigDefaultClauseExample, UnmappedLibraryOnTheListSuppliesNothing) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_FALSE(DesignHoldsCell(d.unit, "adder", "unmappedLib"));
  ASSERT_FALSE(DesignHoldsCell(d.unit, "m", "unmappedLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgUnmappedFirst));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "gateLib");
  auto* f1 = ChildBoundTo(a1, "f1");
  ASSERT_NE(f1, nullptr);
  EXPECT_EQ(f1->library, "gateLib");
}

struct TwoLibraryCell {
  std::string base;
  std::string gate;
  std::string rtl;
  std::string top;
};

TwoLibraryCell AlikeInBothLibraries(std::string_view base,
                                    std::string_view cell,
                                    std::string_view top) {
  TwoLibraryCell pair;
  pair.base = base;
  pair.gate = cell;
  pair.rtl = cell;
  pair.top = top;
  return pair;
}

TwoLibraryCell DifferentInEachLibrary(std::string_view base,
                                      std::string_view gate,
                                      std::string_view rtl,
                                      std::string_view top) {
  TwoLibraryCell pair;
  pair.base = base;
  pair.gate = gate;
  pair.rtl = rtl;
  pair.top = top;
  return pair;
}

RtlirDesign* ElaborateTwoLibraryCell(ScratchDir& tmp, LibraryDesign& d,
                                     const TwoLibraryCell& c,
                                     std::string_view liblist) {
  std::string map_text = "library gateLib " + c.base + ".vg;\n";
  map_text += "library rtlLib top.v, " + c.base + ".v;\n";
  auto map_file = tmp.Write("lib.map", map_text);
  auto gate = tmp.Write(c.base + ".vg", c.gate);
  auto rtl = tmp.Write(c.base + ".v", c.rtl);
  auto top = tmp.Write("top.v", c.top);
  if (!d.map.LoadMapFile(map_file)) return nullptr;
  if (!d.AddFile(gate, c.gate) || !d.AddFile(rtl, c.rtl)) return nullptr;
  if (!d.AddFile(top, c.top)) return nullptr;
  return ElaborateConfigText(tmp, d, DefaultClauseConfig(liblist));
}

constexpr const char* kPrimAsModule =
    "module w(output y, input a);\n"
    "  assign y = ~a;\n"
    "endmodule\n";

TEST(ConfigDefaultClauseExample, ListedInterfaceCopyWinsOverUnlistedOne) {
  ScratchDir tmp;
  LibraryDesign d;
  auto cell = AlikeInBothLibraries("bus", kBusCell, kBusTop);
  auto* top = OnlyTop(ElaborateTwoLibraryCell(tmp, d, cell, "rtlLib"));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "bus", "gateLib"));
  auto* bound = ChildBoundTo(top, "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "rtlLib");
}

TEST(ConfigDefaultClauseExample, ListedProgramCopyWinsOverUnlistedOne) {
  ScratchDir tmp;
  LibraryDesign d;
  auto cell = AlikeInBothLibraries("pgm", kPgmCell, kPgmTop);
  auto* top = OnlyTop(ElaborateTwoLibraryCell(tmp, d, cell, "rtlLib"));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "pgm", "gateLib"));
  auto* bound = ChildBoundTo(top, "p");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "rtlLib");
}

TEST(ConfigDefaultClauseExample, ListedCheckerCopyWinsOverUnlistedOne) {
  ScratchDir tmp;
  LibraryDesign d;
  auto cell = AlikeInBothLibraries("chk", kChkCell, kChkTop);
  auto* top = OnlyTop(ElaborateTwoLibraryCell(tmp, d, cell, "rtlLib"));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "chk", "gateLib"));
  auto* bound = ChildBoundTo(top, "c1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "rtlLib");
}

TEST(ConfigDefaultClauseExample, UnlistedPrimitiveLeavesTheNameToTheModule) {
  ScratchDir tmp;
  LibraryDesign d;
  auto cell = DifferentInEachLibrary("w", kPrimCell, kPrimAsModule, kPrimTop);
  auto* top = OnlyTop(ElaborateTwoLibraryCell(tmp, d, cell, "rtlLib"));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "w", "gateLib"));
  auto* bound = ChildBoundTo(top, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "rtlLib");
}

TEST(ConfigDefaultClauseExample, ListedPrimitiveTakesTheNameFromTheModule) {
  ScratchDir tmp;
  LibraryDesign d;
  auto cell = DifferentInEachLibrary("w", kPrimCell, kPrimAsModule, kPrimTop);
  auto* top = OnlyTop(ElaborateTwoLibraryCell(tmp, d, cell, "gateLib rtlLib"));
  ASSERT_NE(top, nullptr);
  EXPECT_FALSE(d.diag.HasErrors());
  EXPECT_TRUE(top->children.empty());
}

constexpr const char* kSpareCell = "module spare;\nendmodule\n";

TEST(ConfigDefaultClauseExample, NarrowerClauseDoesNotUndoTheExclusion) {
  ScratchDir tmp;
  LibraryDesign d;
  auto map_file = tmp.Write("lib.map",
                            "library gateLib bus.vg;\n"
                            "library rtlLib top.v;\n"
                            "library aLib spare.v;\n");
  auto gate = tmp.Write("bus.vg", kBusCell);
  auto spare = tmp.Write("spare.v", kSpareCell);
  auto top_file = tmp.Write("top.v", kBusTop);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(gate, kBusCell));
  ASSERT_TRUE(d.AddFile(spare, kSpareCell));
  ASSERT_TRUE(d.AddFile(top_file, kBusTop));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "bus", "gateLib"));
  ASSERT_FALSE(DesignHoldsCell(d.unit, "bus", "aLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgCellClauseElsewhere));
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(ChildBoundTo(top, "b"), nullptr);
  EXPECT_TRUE(
      ReportedError(d.diag.Diagnostics(),
                    "unknown module 'bus': the configuration's library list "
                    "(aLib) holds no cell 'bus' for instance 'top.b'",
                    2, "33.4.1.5"));
}

}  // namespace
