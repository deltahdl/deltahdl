#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

constexpr const char* kTopSource =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kAdderSource =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kConfigWithCellClause =
    "config cfg3;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  cell m use gateLib.m;\n"
    "endconfig\n";

constexpr const char* kConfigWithoutCellClause =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kConfigMissingTarget =
    "config cfg7;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  cell m use gateLib.nosuch;\n"
    "endconfig\n";

bool BuildExampleDesign(ScratchDir& tmp, LibraryDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  auto gate_path = tmp.Write("adder.vg", kAdderSource);
  auto rtl_path = tmp.Write("adder.v", kAdderSource);
  auto top_path = tmp.Write("top.v", kTopSource);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.AddFile(gate_path, kAdderSource)) return false;
  if (!design.AddFile(rtl_path, kAdderSource)) return false;
  return design.AddFile(top_path, kTopSource);
}

std::vector<std::string> LibrariesBindingM(RtlirModule* top) {
  return LibrariesBoundBeneath(top, {"a1", "a2"}, {"f1", "f2"});
}

TEST(ConfigCellClauseExample, CellClauseBindsEveryCellOfTheSelectedName) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "aLib"));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "rtlLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, design, kConfigWithCellClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  std::vector<std::string> expected(4, "gateLib");
  EXPECT_EQ(LibrariesBindingM(top), expected);
}

TEST(ConfigCellClauseExample, WithoutTheCellClauseTheListSuppliesEveryCell) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "gateLib"));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigWithoutCellClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  std::vector<std::string> expected(4, "aLib");
  EXPECT_EQ(LibrariesBindingM(top), expected);
}

TEST(ConfigCellClauseExample, CellsOfAnotherNameAreLeftToTheDefaultClause) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "adder", "gateLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, design, kConfigWithCellClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "rtlLib");
  auto* first = ChildBoundTo(top, "a1");
  auto* second = ChildBoundTo(top, "a2");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->name, "adder");
  EXPECT_EQ(first->library, "aLib");
  EXPECT_EQ(second->library, "aLib");
}

TEST(ConfigCellClauseExample, UseExpansionNamingNoCellLeavesTheCellsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "aLib"));
  ASSERT_FALSE(DesignHoldsCell(design.unit, "nosuch", "gateLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, design, kConfigMissingTarget));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(),
                            "library 'gateLib' holds no cell 'nosuch'", 2,
                            "33.4.1.6"));
  std::vector<std::string> expected(4, "");
  EXPECT_EQ(LibrariesBindingM(top), expected);
}

struct SoloCell {
  std::string base;
  std::string text;
  std::string top;
};

std::string CellUseGateLib(std::string_view name) {
  std::string clause = "  cell ";
  clause += name;
  clause += " use gateLib.";
  clause += name;
  clause += ";\n";
  return clause;
}

std::string SoloCellConfig(std::string_view cell_clause) {
  std::string text = "config cfg;\n";
  text += "  design rtlLib.top;\n";
  text += "  default liblist rtlLib;\n";
  text += cell_clause;
  text += "endconfig\n";
  return text;
}

RtlirDesign* ElaborateSoloCell(ScratchDir& tmp, LibraryDesign& design,
                               const SoloCell& cell,
                               std::string_view cell_clause) {
  if (!BuildTwoLibraryDesign(tmp, design, cell.base, cell.text, cell.top)) {
    return nullptr;
  }
  return ElaborateConfigText(tmp, design, SoloCellConfig(cell_clause));
}

constexpr const char* kNoCellClause = "";

constexpr const char* kInterfaceCell = "interface bus;\nendinterface\n";
constexpr const char* kInterfaceTop = "module top;\n  bus b();\nendmodule\n";

constexpr const char* kProgramCell = "program pgm;\nendprogram\n";
constexpr const char* kProgramTop = "module top;\n  pgm p();\nendmodule\n";

constexpr const char* kCheckerCell = "checker chk;\nendchecker\n";
constexpr const char* kCheckerTop = "module top;\n  chk c1();\nendmodule\n";

constexpr const char* kPrimitiveCell =
    "primitive w(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";
constexpr const char* kPrimitiveTop =
    "module top;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w u(y, a);\n"
    "endmodule\n";

TEST(ConfigCellClauseExample, CellClauseBindsAnInterfacePastTheList) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "bus", .text = kInterfaceCell, .top = kInterfaceTop};
  auto* top =
      OnlyTop(ElaborateSoloCell(tmp, design, cell, CellUseGateLib("bus")));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigCellClauseExample, WithoutTheClauseTheInterfaceIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "bus", .text = kInterfaceCell, .top = kInterfaceTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "b"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'bus': the configuration's default library "
                    "list (rtlLib) holds no cell 'bus' for instance 'top.b'",
                    2, "33.4.1.5"));
}

TEST(ConfigCellClauseExample, CellClauseBindsAProgramPastTheList) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "pgm", .text = kProgramCell, .top = kProgramTop};
  auto* top =
      OnlyTop(ElaborateSoloCell(tmp, design, cell, CellUseGateLib("pgm")));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "p");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigCellClauseExample, WithoutTheClauseTheProgramIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "pgm", .text = kProgramCell, .top = kProgramTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "p"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'pgm': the configuration's default library "
                    "list (rtlLib) holds no cell 'pgm' for instance 'top.p'",
                    2, "33.4.1.5"));
}

TEST(ConfigCellClauseExample, CellClauseBindsACheckerPastTheList) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "chk", .text = kCheckerCell, .top = kCheckerTop};
  auto* top =
      OnlyTop(ElaborateSoloCell(tmp, design, cell, CellUseGateLib("chk")));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "c1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigCellClauseExample, WithoutTheClauseTheCheckerIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "chk", .text = kCheckerCell, .top = kCheckerTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "c1"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'chk': the configuration's default library "
                    "list (rtlLib) holds no cell 'chk' for instance 'top.c1'",
                    2, "33.4.1.5"));
}

TEST(ConfigCellClauseExample, CellClauseBindsAPrimitivePastTheList) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "w", .text = kPrimitiveCell, .top = kPrimitiveTop};
  auto* top =
      OnlyTop(ElaborateSoloCell(tmp, design, cell, CellUseGateLib("w")));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(top->children.empty());
}

TEST(ConfigCellClauseExample, WithoutTheClauseThePrimitiveIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "w", .text = kPrimitiveCell, .top = kPrimitiveTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(),
                            "default library list (rtlLib) holds no cell 'w'",
                            4, "33.4.1.5"));
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

constexpr const char* kRivalModule =
    "module w(output y, input a);\n"
    "  assign y = ~a;\n"
    "endmodule\n";

RtlirDesign* ElaborateRivalCells(ScratchDir& tmp, LibraryDesign& design,
                                 std::string_view cell_clause) {
  auto map_path = tmp.Write("lib.map",
                            "library rtlLib top.v, w.v;\n"
                            "library gateLib w.vg;\n");
  auto primitive_path = tmp.Write("w.v", kPrimitiveCell);
  auto module_path = tmp.Write("w.vg", kRivalModule);
  auto top_path = tmp.Write("top.v", kPrimitiveTop);
  if (!design.map.LoadMapFile(map_path)) return nullptr;
  if (!design.AddFile(primitive_path, kPrimitiveCell)) return nullptr;
  if (!design.AddFile(module_path, kRivalModule)) return nullptr;
  if (!design.AddFile(top_path, kPrimitiveTop)) return nullptr;
  std::string config = "config cfg;\n";
  config += "  design rtlLib.top;\n";
  config += "  default liblist rtlLib gateLib;\n";
  config += cell_clause;
  config += "endconfig\n";
  return ElaborateConfigText(tmp, design, config);
}

TEST(ConfigCellClauseExample, CellClauseNamingAModuleLeavesTheNameNoPrimitive) {
  ScratchDir tmp;
  LibraryDesign design;
  auto* top = OnlyTop(ElaborateRivalCells(tmp, design, CellUseGateLib("w")));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "rtlLib"));
  EXPECT_FALSE(design.diag.HasErrors());
  auto* bound = ChildBoundTo(top, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "w");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigCellClauseExample, WithoutTheClauseTheListedPrimitiveTakesTheName) {
  ScratchDir tmp;
  LibraryDesign design;
  auto* top = OnlyTop(ElaborateRivalCells(tmp, design, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(top->children.empty());
}

}  // namespace
