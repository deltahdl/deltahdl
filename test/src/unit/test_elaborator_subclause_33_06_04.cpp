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

constexpr const char* kConfigWithInstanceClause =
    "config cfg4;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a2 liblist aLib;\n"
    "endconfig\n";

constexpr const char* kConfigWithoutInstanceClause =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kConfigPathNamingNoInstance =
    "config cfg8;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a liblist aLib;\n"
    "endconfig\n";

constexpr const char* kConfigDeeperInstancePath =
    "config cfg9;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a1.f1 liblist aLib;\n"
    "endconfig\n";

bool BuildExampleDesign(ScratchDir& tmp, LibraryDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  auto rtl_path = tmp.Write("adder.v", kAdderSource);
  auto gate_path = tmp.Write("adder.vg", kAdderSource);
  auto top_path = tmp.Write("top.v", kTopSource);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.AddFile(rtl_path, kAdderSource)) return false;
  if (!design.AddFile(gate_path, kAdderSource)) return false;
  return design.AddFile(top_path, kTopSource);
}

std::vector<std::string> LibrariesBindingTheAdders(RtlirModule* top) {
  return LibrariesBound(top, {"a1", "a2"});
}

std::vector<std::string> LibrariesBindingM(RtlirModule* top) {
  return LibrariesBoundBeneath(top, {"a1", "a2"}, {"f1", "f2"});
}

TEST(ConfigInstanceClauseExample, NamedInstanceIsBoundOutOfTheClausesOwnList) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "adder", "gateLib"));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "adder", "aLib"));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigWithInstanceClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* second = ChildBoundTo(top, "a2");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->name, "adder");
  EXPECT_EQ(second->library, "aLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseBothAddersFollowTheDefault) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "adder", "aLib"));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigWithoutInstanceClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  std::vector<std::string> expected(2, "gateLib");
  EXPECT_EQ(LibrariesBindingTheAdders(top), expected);
}

TEST(ConfigInstanceClauseExample, DescendantsOfTheNamedInstanceInheritItsList) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "gateLib"));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "rtlLib"));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigWithInstanceClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  std::vector<std::string> expected{"gateLib", "gateLib", "aLib", "aLib"};
  EXPECT_EQ(LibrariesBindingM(top), expected);
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseEveryDescendantFollowsIt) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "aLib"));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigWithoutInstanceClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  std::vector<std::string> expected(4, "gateLib");
  EXPECT_EQ(LibrariesBindingM(top), expected);
}

TEST(ConfigInstanceClauseExample, InstancesOutsideTheClauseKeepTheDefault) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigWithInstanceClause));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "rtlLib");
  auto* first = ChildBoundTo(top, "a1");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->library, "gateLib");
  auto* leaf = ChildBoundTo(first, "f1");
  auto* other_leaf = ChildBoundTo(first, "f2");
  ASSERT_NE(leaf, nullptr);
  ASSERT_NE(other_leaf, nullptr);
  EXPECT_EQ(leaf->library, "gateLib");
  EXPECT_EQ(other_leaf->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, PathNamingNoInstanceGovernsNoBinding) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "aLib"));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigPathNamingNoInstance));
  ASSERT_NE(top, nullptr);
  std::vector<std::string> adders(2, "gateLib");
  EXPECT_EQ(LibrariesBindingTheAdders(top), adders);
  std::vector<std::string> leaves(4, "gateLib");
  EXPECT_EQ(LibrariesBindingM(top), leaves);
}

TEST(ConfigInstanceClauseExample, ClauseNamingADeeperInstanceReachesOnlyIt) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "gateLib"));

  auto* top =
      OnlyTop(ElaborateConfigText(tmp, design, kConfigDeeperInstancePath));
  ASSERT_FALSE(design.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  std::vector<std::string> adders(2, "gateLib");
  EXPECT_EQ(LibrariesBindingTheAdders(top), adders);
  std::vector<std::string> expected{"aLib", "gateLib", "gateLib", "gateLib"};
  EXPECT_EQ(LibrariesBindingM(top), expected);
}

struct NestedCell {
  std::string base;
  std::string text;
  std::string top;
};

constexpr const char* kInstanceClauseReachingGateLib =
    "  instance top.m1 liblist rtlLib gateLib;\n";

constexpr const char* kNoInstanceClause = "";

RtlirDesign* ElaborateNestedCell(ScratchDir& tmp, LibraryDesign& design,
                                 const NestedCell& cell,
                                 std::string_view inst_clause) {
  if (!BuildTwoLibraryDesign(tmp, design, cell.base, cell.text, cell.top)) {
    return nullptr;
  }
  std::string config = "config cfg;\n";
  config += "  design rtlLib.top;\n";
  config += "  default liblist rtlLib;\n";
  config += inst_clause;
  config += "endconfig\n";
  return ElaborateConfigText(tmp, design, config);
}

RtlirModule* NamedInstanceOf(RtlirDesign* design) {
  auto* top = OnlyTop(design);
  if (top == nullptr) return nullptr;
  return ChildBoundTo(top, "m1");
}

constexpr const char* kInterfaceCell = "interface bus;\nendinterface\n";
constexpr const char* kInterfaceTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  bus b();\n"
    "endmodule\n";

constexpr const char* kProgramCell = "program pgm;\nendprogram\n";
constexpr const char* kProgramTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  pgm p();\n"
    "endmodule\n";

constexpr const char* kCheckerCell = "checker chk;\nendchecker\n";
constexpr const char* kCheckerTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  chk c1();\n"
    "endmodule\n";

constexpr const char* kPrimitiveCell =
    "primitive w(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";
constexpr const char* kPrimitiveTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w u(y, a);\n"
    "endmodule\n";

constexpr const char* kDeepCell = "module leaf;\nendmodule\n";
constexpr const char* kDeepTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  sub s();\n"
    "endmodule\n"
    "module sub;\n"
    "  leaf u();\n"
    "endmodule\n";

TEST(ConfigInstanceClauseExample, InheritedListSuppliesAnInterface) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "bus", .text = kInterfaceCell, .top = kInterfaceTop};
  auto* elaborated =
      ElaborateNestedCell(tmp, design, cell, kInstanceClauseReachingGateLib);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  auto* bound = ChildBoundTo(mid, "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheInterfaceIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "bus", .text = kInterfaceCell, .top = kInterfaceTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(mid, "b"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'bus': the configuration's default library "
                    "list (rtlLib) holds no cell 'bus' for instance 'top.m1.b'",
                    5, "33.4.1.5"));
}

TEST(ConfigInstanceClauseExample, InheritedListSuppliesAProgram) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "pgm", .text = kProgramCell, .top = kProgramTop};
  auto* elaborated =
      ElaborateNestedCell(tmp, design, cell, kInstanceClauseReachingGateLib);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  auto* bound = ChildBoundTo(mid, "p");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheProgramIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "pgm", .text = kProgramCell, .top = kProgramTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(mid, "p"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'pgm': the configuration's default library "
                    "list (rtlLib) holds no cell 'pgm' for instance 'top.m1.p'",
                    5, "33.4.1.5"));
}

TEST(ConfigInstanceClauseExample, InheritedListSuppliesAChecker) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "chk", .text = kCheckerCell, .top = kCheckerTop};
  auto* elaborated =
      ElaborateNestedCell(tmp, design, cell, kInstanceClauseReachingGateLib);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  auto* bound = ChildBoundTo(mid, "c1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheCheckerIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "chk", .text = kCheckerCell, .top = kCheckerTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(mid, "c1"), nullptr);
  EXPECT_TRUE(ReportedError(
      design.diag.Diagnostics(),
      "unknown module 'chk': the configuration's default library list (rtlLib) "
      "holds no cell 'chk' for instance 'top.m1.c1'",
      5, "33.4.1.5"));
}

TEST(ConfigInstanceClauseExample, InheritedListSuppliesAPrimitive) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "w", .text = kPrimitiveCell, .top = kPrimitiveTop};
  auto* elaborated =
      ElaborateNestedCell(tmp, design, cell, kInstanceClauseReachingGateLib);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(mid->children.empty());
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseThePrimitiveIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "w", .text = kPrimitiveCell, .top = kPrimitiveTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(),
                            "default library list (rtlLib) holds no cell 'w'",
                            7, "33.4.1.5"));
  ASSERT_EQ(mid->children.size(), 1u);
  EXPECT_EQ(mid->children[0].resolved, nullptr);
}

TEST(ConfigInstanceClauseExample, InheritedListReachesBeyondTheFirstLevel) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "leaf", .text = kDeepCell, .top = kDeepTop};
  auto* elaborated =
      ElaborateNestedCell(tmp, design, cell, kInstanceClauseReachingGateLib);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  auto* sub = ChildBoundTo(mid, "s");
  ASSERT_NE(sub, nullptr);
  EXPECT_EQ(sub->library, "rtlLib");
  auto* bound = ChildBoundTo(sub, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "leaf");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheDeepCellIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "leaf", .text = kDeepCell, .top = kDeepTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "leaf", "gateLib"));
  auto* sub = ChildBoundTo(mid, "s");
  ASSERT_NE(sub, nullptr);
  EXPECT_EQ(ChildBoundTo(sub, "u"), nullptr);
  EXPECT_TRUE(ReportedError(
      design.diag.Diagnostics(),
      "unknown module 'leaf': the configuration's default library list "
      "(rtlLib) holds no cell 'leaf' for instance 'top.m1.s.u'",
      8, "33.4.1.5"));
}

constexpr const char* kNarrowedTopSource =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  leaf u();\n"
    "endmodule\n";

constexpr const char* kInstanceClauseWithoutTheLeaf =
    "  instance top.m1 liblist rtlLib;\n";

RtlirDesign* ElaborateNarrowedSubtree(ScratchDir& tmp, LibraryDesign& design,
                                      std::string_view inst_clause) {
  auto map_path = tmp.Write("lib.map",
                            "library rtlLib top.v;\n"
                            "library gateLib leaf.vg;\n");
  auto gate_path = tmp.Write("leaf.vg", kDeepCell);
  auto top_path = tmp.Write("top.v", kNarrowedTopSource);
  if (!design.map.LoadMapFile(map_path)) return nullptr;
  if (!design.AddFile(gate_path, kDeepCell)) return nullptr;
  if (!design.AddFile(top_path, kNarrowedTopSource)) return nullptr;
  std::string config = "config cfg;\n";
  config += "  design rtlLib.top;\n";
  config += "  default liblist rtlLib gateLib;\n";
  config += inst_clause;
  config += "endconfig\n";
  return ElaborateConfigText(tmp, design, config);
}

TEST(ConfigInstanceClauseExample, InheritedListWithoutTheCellLeavesItUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  auto* elaborated =
      ElaborateNarrowedSubtree(tmp, design, kInstanceClauseWithoutTheLeaf);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "leaf", "gateLib"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(),
                            "library list (rtlLib) holds no cell 'leaf' for "
                            "instance 'top.m1.u'",
                            5, "33.4.1.5"));
  EXPECT_EQ(ChildBoundTo(mid, "u"), nullptr);
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheDefaultListFindsTheCell) {
  ScratchDir tmp;
  LibraryDesign design;
  auto* elaborated = ElaborateNarrowedSubtree(tmp, design, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  EXPECT_FALSE(design.diag.HasErrors());
  auto* bound = ChildBoundTo(mid, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

constexpr const char* kClauseListWithoutTheCell =
    "  instance top.m1 liblist gateLib;\n";

TEST(ConfigInstanceClauseExample, ClauseListLackingTheCellLeavesItUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  auto* elaborated =
      ElaborateNarrowedSubtree(tmp, design, kClauseListWithoutTheCell);
  auto* top = OnlyTop(elaborated);
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "mid", "rtlLib"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(),
                            "library list (gateLib) holds no cell 'mid' for "
                            "instance 'top.m1'",
                            2, "33.4.1.5"));
  EXPECT_EQ(ChildBoundTo(top, "m1"), nullptr);
}

constexpr const char* kSoloIfaceTop = "module top;\n  bus x();\nendmodule\n";
constexpr const char* kSoloProgTop = "module top;\n  pgm x();\nendmodule\n";
constexpr const char* kSoloChkTop = "module top;\n  chk x();\nendmodule\n";
constexpr const char* kSoloPrimTop =
    "module top;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w x(y, a);\n"
    "endmodule\n";

constexpr const char* kSoloClause =
    "  instance top.x liblist rtlLib gateLib;\n";

TEST(ConfigInstanceClauseExample, ClauseBindsTheNamedInterfaceInstance) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "bus", .text = kInterfaceCell, .top = kSoloIfaceTop};
  auto* top = OnlyTop(ElaborateNestedCell(tmp, design, cell, kSoloClause));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "x");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedInterfaceIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "bus", .text = kInterfaceCell, .top = kSoloIfaceTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "x"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'bus': the configuration's default library "
                    "list (rtlLib) holds no cell 'bus' for instance 'top.x'",
                    2, "33.4.1.5"));
}

TEST(ConfigInstanceClauseExample, ClauseBindsTheNamedProgramInstance) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "pgm", .text = kProgramCell, .top = kSoloProgTop};
  auto* top = OnlyTop(ElaborateNestedCell(tmp, design, cell, kSoloClause));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "x");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedProgramIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "pgm", .text = kProgramCell, .top = kSoloProgTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "x"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'pgm': the configuration's default library "
                    "list (rtlLib) holds no cell 'pgm' for instance 'top.x'",
                    2, "33.4.1.5"));
}

TEST(ConfigInstanceClauseExample, ClauseBindsTheNamedCheckerInstance) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "chk", .text = kCheckerCell, .top = kSoloChkTop};
  auto* top = OnlyTop(ElaborateNestedCell(tmp, design, cell, kSoloClause));
  ASSERT_NE(top, nullptr);
  auto* bound = ChildBoundTo(top, "x");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedCheckerIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "chk", .text = kCheckerCell, .top = kSoloChkTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "x"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'chk': the configuration's default library "
                    "list (rtlLib) holds no cell 'chk' for instance 'top.x'",
                    2, "33.4.1.5"));
}

TEST(ConfigInstanceClauseExample, ClauseBindsTheNamedPrimitiveInstance) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "w", .text = kPrimitiveCell, .top = kSoloPrimTop};
  auto* top = OnlyTop(ElaborateNestedCell(tmp, design, cell, kSoloClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(top->children.empty());
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedPrimitiveIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "w", .text = kPrimitiveCell, .top = kSoloPrimTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(),
                            "default library list (rtlLib) holds no cell 'w'",
                            4, "33.4.1.5"));
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

constexpr const char* kDeepInterfaceCell = "interface leaf;\nendinterface\n";

constexpr const char* kInterfaceLevelTop =
    "module top;\n"
    "  bus m1();\n"
    "endmodule\n"
    "interface bus;\n"
    "  leaf u();\n"
    "endinterface\n";

TEST(ConfigInstanceClauseExample, InheritedListPassesThroughAnInterface) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{
      .base = "leaf", .text = kDeepInterfaceCell, .top = kInterfaceLevelTop};
  auto* elaborated =
      ElaborateNestedCell(tmp, design, cell, kInstanceClauseReachingGateLib);
  auto* bus = NamedInstanceOf(elaborated);
  ASSERT_NE(bus, nullptr);
  EXPECT_TRUE(bus->is_interface);
  auto* bound = ChildBoundTo(bus, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigInstanceClauseExample, WithoutTheClauseTheCellBelowIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{
      .base = "leaf", .text = kDeepInterfaceCell, .top = kInterfaceLevelTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* bus = NamedInstanceOf(elaborated);
  ASSERT_NE(bus, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "leaf", "gateLib"));
  EXPECT_EQ(ChildBoundTo(bus, "u"), nullptr);
  EXPECT_TRUE(ReportedError(
      design.diag.Diagnostics(),
      "unknown module 'leaf': the configuration's default library list "
      "(rtlLib) holds no cell 'leaf' for instance 'top.m1.u'",
      5, "33.4.1.5"));
}

}  // namespace
