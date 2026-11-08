#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator.h"
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

constexpr const char* kAdderFile =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

constexpr const char* kAdderOnlyFile =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n";

bool BuildExampleDesign(ScratchDir& tmp, LibraryDesign& d,
                        const std::string& map_text) {
  auto map_file = tmp.Write("lib.map", map_text);
  auto gate = tmp.Write("adder.vg", kAdderFile);
  auto rtl = tmp.Write("adder.v", kAdderFile);
  auto top = tmp.Write("top.v", kTopFile);
  if (!d.map.LoadMapFile(map_file)) return false;
  return d.AddFile(gate, kAdderFile) && d.AddFile(rtl, kAdderFile) &&
         d.AddFile(top, kTopFile);
}

constexpr const char* kWidgetModuleFile =
    "module w(output y, input a);\n"
    "  assign y = ~a;\n"
    "endmodule\n";
constexpr const char* kWidgetPrimitiveFile =
    "primitive w(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";
constexpr const char* kWidgetTopFile =
    "module top;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w u(y, a);\n"
    "endmodule\n";

struct TwoFileCell {
  std::string base;
  std::string cell;
  std::string top;
};

bool BuildTwoFileCellDesign(ScratchDir& tmp, LibraryDesign& d,
                            const TwoFileCell& c) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library aLib " + c.base + ".v;\n";
  map_text += "library gateLib " + c.base + ".vg;\n";
  auto map_file = tmp.Write("lib.map", map_text);
  auto gate = tmp.Write(c.base + ".vg", c.cell);
  auto rtl = tmp.Write(c.base + ".v", c.cell);
  auto top = tmp.Write("top.v", c.top);
  if (!d.map.LoadMapFile(map_file)) return false;
  return d.AddFile(gate, c.cell) && d.AddFile(rtl, c.cell) &&
         d.AddFile(top, c.top);
}

RtlirDesign* ElaborateUnderMapOrder(LibraryDesign& d,
                                    std::string_view top_cell) {
  Elaborator elab(d.arena, d.diag, d.unit);
  elab.SetLibraryDeclarationOrder(d.map.ResolveSearchOrder({}));
  return elab.Elaborate(top_cell);
}

TEST(DefaultLibraryBinding, EveryAdderInstanceBindsFirstDeclaredLibraryWithIt) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "gateLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
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

TEST(DefaultLibraryBinding, NestedMInstancesBindFirstDeclaredLibraryWithM) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "m", "aLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  ASSERT_NE(a1, nullptr);
  ASSERT_EQ(a1->library, "aLib");
  auto* f1 = ChildBoundTo(a1, "f1");
  auto* f2 = ChildBoundTo(a1, "f2");
  ASSERT_NE(f1, nullptr);
  ASSERT_NE(f2, nullptr);
  EXPECT_EQ(f1->name, "m");
  EXPECT_EQ(f1->library, "rtlLib");
  EXPECT_EQ(f2->library, "rtlLib");

  auto* a2 = ChildBoundTo(top, "a2");
  ASSERT_NE(a2, nullptr);
  auto* g1 = ChildBoundTo(a2, "f1");
  auto* g2 = ChildBoundTo(a2, "f2");
  ASSERT_NE(g1, nullptr);
  ASSERT_NE(g2, nullptr);
  EXPECT_EQ(g1->library, "rtlLib");
  EXPECT_EQ(g2->library, "rtlLib");
}

TEST(DefaultLibraryBinding, DeclarationOrderAloneDecidesWhichAdderIsBound) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d,
                                 "library rtlLib top.v;\n"
                                 "library gateLib adder.vg;\n"
                                 "library aLib adder.*;\n"));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "aLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "gateLib");
}

TEST(DefaultLibraryBinding, DesignElaboratedFromACellNameUsesDeclarationOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));
  const std::string kConfigCell =
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  default liblist gateLib;\n"
      "endconfig\n";
  auto cfg_file = tmp.Write("cfg.sv", kConfigCell);
  ASSERT_TRUE(d.AddFile(cfg_file, kConfigCell));
  ASSERT_EQ(d.unit->configs.size(), 1u);

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "aLib");
}

TEST(DefaultLibraryBinding, TopCellComesFromFirstDeclaredLibraryHoldingIt) {
  ScratchDir tmp;
  LibraryDesign d;
  const std::string kTopCell = "module top;\nendmodule\n";
  auto map_file = tmp.Write("lib.map",
                            "library gateLib top.vg;\n"
                            "library rtlLib top.v;\n");
  auto gate = tmp.Write("top.vg", kTopCell);
  auto rtl = tmp.Write("top.v", kTopCell);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(rtl, kTopCell));
  ASSERT_TRUE(d.AddFile(gate, kTopCell));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "top", "rtlLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "gateLib");
}

TEST(DefaultLibraryBinding, InterfaceCellIsSearchedInDeclarationOrderToo) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(
      BuildTwoFileCellDesign(tmp, d,
                             {.base = "bus",
                              .cell = "interface bus;\nendinterface\n",
                              .top = "module top;\n  bus b();\nendmodule\n"}));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "bus", "gateLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "aLib");
}

TEST(DefaultLibraryBinding, ProgramCellIsSearchedInDeclarationOrderToo) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(
      BuildTwoFileCellDesign(tmp, d,
                             {.base = "pgm",
                              .cell = "program pgm;\nendprogram\n",
                              .top = "module top;\n  pgm p();\nendmodule\n"}));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "pgm", "gateLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "p");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "aLib");
}

TEST(DefaultLibraryBinding, CheckerCellIsSearchedInDeclarationOrderToo) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(
      BuildTwoFileCellDesign(tmp, d,
                             {.base = "chk",
                              .cell = "checker chk;\nendchecker\n",
                              .top = "module top;\n  chk c1();\nendmodule\n"}));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "chk", "gateLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "c1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "aLib");
}

TEST(DefaultLibraryBinding, UndeclaredLibraryIsSearchedAfterTheDeclaredOnes) {
  ScratchDir tmp;
  LibraryDesign d;
  auto map_file = tmp.Write("lib.map", kExampleMap);
  auto spare = tmp.Write("spare.sv", kAdderFile);
  auto gate = tmp.Write("adder.vg", kAdderFile);
  auto rtl = tmp.Write("adder.v", kAdderFile);
  auto top_file = tmp.Write("top.v", kTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(spare, kAdderFile));
  ASSERT_TRUE(d.AddFile(gate, kAdderFile));
  ASSERT_TRUE(d.AddFile(rtl, kAdderFile));
  ASSERT_TRUE(d.AddFile(top_file, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "work"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "aLib");
}

TEST(DefaultLibraryBinding, PrimitiveInAnEarlierLibraryTakesTheName) {
  ScratchDir tmp;
  LibraryDesign d;
  auto map_file = tmp.Write("lib.map",
                            "library rtlLib top.v;\n"
                            "library aLib w.v;\n"
                            "library gateLib w.vg;\n");
  auto gate = tmp.Write("w.vg", kWidgetModuleFile);
  auto rtl = tmp.Write("w.v", kWidgetPrimitiveFile);
  auto top_file = tmp.Write("top.v", kWidgetTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(gate, kWidgetModuleFile));
  ASSERT_TRUE(d.AddFile(rtl, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.AddFile(top_file, kWidgetTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "w", "gateLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->children.empty());
}

TEST(DefaultLibraryBinding, ModuleInAnEarlierLibraryKeepsTheNameFromPrimitive) {
  ScratchDir tmp;
  LibraryDesign d;
  auto map_file = tmp.Write("lib.map",
                            "library rtlLib top.v;\n"
                            "library aLib w.v;\n"
                            "library gateLib w.vg;\n");
  auto gate = tmp.Write("w.vg", kWidgetPrimitiveFile);
  auto rtl = tmp.Write("w.v", kWidgetModuleFile);
  auto top_file = tmp.Write("top.v", kWidgetTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(gate, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.AddFile(rtl, kWidgetModuleFile));
  ASSERT_TRUE(d.AddFile(top_file, kWidgetTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "w", "gateLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "aLib");
}

TEST(DefaultLibraryBinding, NearestPrimitiveIsWhatOtherKindsAreMeasuredBy) {
  ScratchDir tmp;
  LibraryDesign d;
  auto map_file = tmp.Write("lib.map",
                            "library libA prim_a.v;\n"
                            "library libB w.v;\n"
                            "library libC prim_c.v;\n"
                            "library libD prim_d.v, top.v;\n");
  auto last = tmp.Write("prim_d.v", kWidgetPrimitiveFile);
  auto first = tmp.Write("prim_a.v", kWidgetPrimitiveFile);
  auto middle = tmp.Write("prim_c.v", kWidgetPrimitiveFile);
  auto module_file = tmp.Write("w.v", kWidgetModuleFile);
  auto top_file = tmp.Write("top.v", kWidgetTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(last, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.AddFile(first, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.AddFile(middle, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.AddFile(module_file, kWidgetModuleFile));
  ASSERT_TRUE(d.AddFile(top_file, kWidgetTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "w", "libB"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->children.empty());
}

TEST(DefaultLibraryBinding, LibraryNamedTwiceKeepsItsFirstPosition) {
  ScratchDir tmp;
  LibraryDesign d;
  auto map_file = tmp.Write("lib.map",
                            "library rtlLib top.v;\n"
                            "library aLib adder.*;\n"
                            "library rtlLib extra.v;\n"
                            "library gateLib adder.vg;\n");
  auto gate = tmp.Write("adder.vg", kAdderFile);
  auto rtl = tmp.Write("adder.v", kAdderFile);
  auto extra = tmp.Write("extra.v", kAdderOnlyFile);
  auto top_file = tmp.Write("top.v", kTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(gate, kAdderFile));
  ASSERT_TRUE(d.AddFile(rtl, kAdderFile));
  ASSERT_TRUE(d.AddFile(extra, kAdderOnlyFile));
  ASSERT_TRUE(d.AddFile(top_file, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "aLib"));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = ChildBoundTo(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "rtlLib");
}

TEST(DefaultLibraryBinding, InstanceOfACellNoLibraryHoldsIsLeftUnbound) {
  ScratchDir tmp;
  LibraryDesign d;
  const std::string kTopCell = "module top;\n  subtractor s1();\nendmodule\n";
  auto map_file = tmp.Write("lib.map", kExampleMap);
  auto top_file = tmp.Write("top.v", kTopCell);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.AddFile(top_file, kTopCell));

  auto* top = OnlyTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(ReportedError(d.diag.Diagnostics(), "unknown module 'subtractor'",
                            2, "23.3.2"));
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

TEST(DefaultLibraryBinding, RootCellNoLibraryHoldsYieldsNoDesign) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));

  auto* design = ElaborateUnderMapOrder(d, "subtractor");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(d.diag.Diagnostics(),
                            "top module 'subtractor' not found", 0, ""));
}

}  // namespace
