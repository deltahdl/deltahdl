#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

constexpr const char* kInnerConfig =
    "config cfg5;\n"
    "  design aLib.adder;\n"
    "  default liblist gateLib aLib;\n"
    "  instance adder.f1 liblist rtlLib;\n"
    "endconfig\n";

constexpr const char* kDelegatingConfig =
    "config cfg6;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 use work.cfg5:config;\n"
    "endconfig\n";

constexpr const char* kPlainConfig =
    "config cfg7;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kGatePreferringDelegating =
    "config cfg8;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a2 use work.cfg5:config;\n"
    "endconfig\n";

constexpr const char* kGatePreferringPlain =
    "config cfg9;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kDelegatingToUnknownConfig =
    "config cfg10;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 use work.nosuch:config;\n"
    "endconfig\n";

constexpr const char* kOuterRelativeInnerConfig =
    "config cfg11;\n"
    "  design aLib.adder;\n"
    "  default liblist gateLib aLib;\n"
    "  instance top.a2.f1 liblist rtlLib;\n"
    "endconfig\n";

constexpr const char* kDelegatingToOuterRelative =
    "config cfg12;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 use work.cfg11:config;\n"
    "endconfig\n";

bool BuildExampleDesign(ScratchDir& tmp, LibraryDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, "adder.v", kAdderSource)) return false;
  if (!design.Add(tmp, "adder.vg", kAdderSource)) return false;
  return design.Add(tmp, "top.v", kTopSource);
}

std::string Both(const char* first, const char* second) {
  return std::string(first) + second;
}

TEST(ConfigHierarchicalConfigExample, ConfigForTheAdderAloneBindsItsOwnCells) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto config = kInnerConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg5");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* top = OnlyTop(elaborated);
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->name, "adder");
  EXPECT_EQ(top->library, "aLib");
  auto* first = CellAt(elaborated, "f1");
  auto* second = CellAt(elaborated, "f2");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->library, "rtlLib");
  EXPECT_EQ(second->library, "gateLib");
}

TEST(ConfigHierarchicalConfigExample, DelegatedDesignStatementBindsInstance) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "adder", "gateLib"));

  auto config = Both(kInnerConfig, kGatePreferringDelegating);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg8");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* bound = CellAt(elaborated, "a2");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "adder");
  EXPECT_EQ(bound->library, "aLib");
}

TEST(ConfigHierarchicalConfigExample, WithoutDelegationTheInstanceTakesList) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "adder", "aLib"));

  auto config = kGatePreferringPlain;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg9");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* bound = CellAt(elaborated, "a2");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigHierarchicalConfigExample, DelegatedDefaultClauseBindsDescendants) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "gateLib"));

  auto config = Both(kInnerConfig, kDelegatingConfig);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg6");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* bound = CellAt(elaborated, "a2.f2");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "m");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigHierarchicalConfigExample, DelegatedInstanceClauseBindsItsOwnPath) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "rtlLib"));

  auto config = Both(kInnerConfig, kDelegatingConfig);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg6");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* bound = CellAt(elaborated, "a2.f1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "m");
  EXPECT_EQ(bound->library, "rtlLib");
}

TEST(ConfigHierarchicalConfigExample, WithoutDelegationDescendantsTakeTheList) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "aLib"));

  auto config = kPlainConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg7");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* first = CellAt(elaborated, "a2.f1");
  auto* second = CellAt(elaborated, "a2.f2");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->library, "aLib");
  EXPECT_EQ(second->library, "aLib");
}

TEST(ConfigHierarchicalConfigExample, DelegationLeavesTheSiblingSubtreeAlone) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto config = Both(kInnerConfig, kDelegatingConfig);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg6");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* top = OnlyTop(elaborated);
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "rtlLib");
  auto* sibling = CellAt(elaborated, "a1");
  auto* first = CellAt(elaborated, "a1.f1");
  auto* second = CellAt(elaborated, "a1.f2");
  ASSERT_NE(sibling, nullptr);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(sibling->library, "aLib");
  EXPECT_EQ(first->library, "aLib");
  EXPECT_EQ(second->library, "aLib");
}

::testing::AssertionResult ReportedOuterRelativePath(LibraryDesign& design) {
  return ReportedError(design.diag.Diagnostics(),
                       "instance path 'top.a2.f1' in config 'cfg11' does not "
                       "start at a top-level cell of the config's design "
                       "statement",
                       4, "33.4.1.3");
}

TEST(ConfigHierarchicalConfigExample, DelegatedPathAgainstOuterTopIsReported) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto config = Both(kOuterRelativeInnerConfig, kDelegatingToOuterRelative);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg12");
  EXPECT_NE(elaborated, nullptr);
  EXPECT_TRUE(ReportedOuterRelativePath(design));
}

TEST(ConfigHierarchicalConfigExample, DelegatedPathAgainstOuterTopSelectsNone) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "rtlLib"));

  auto config = Both(kOuterRelativeInnerConfig, kDelegatingToOuterRelative);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg12");
  auto* bound = CellAt(elaborated, "a2.f1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
  EXPECT_TRUE(ReportedOuterRelativePath(design));
}

TEST(ConfigHierarchicalConfigExample, DelegationToAnUnknownConfigIsReported) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto config = kDelegatingToUnknownConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg10");
  EXPECT_NE(elaborated, nullptr);
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(),
                            "config 'cfg10' delegates instance 'top.a2' to "
                            "unknown config 'nosuch'",
                            4, "33.4.2"));
}

struct DelegatedCell {
  std::string base;
  const char* text;
  const char* top;
};

bool BuildSoloCellDesign(ScratchDir& tmp, LibraryDesign& design,
                         const DelegatedCell& cell) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library gateLib " + cell.base + ".vg;\n";
  auto map_path = tmp.Write("lib.map", map_text);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, cell.base + ".vg", cell.text)) return false;
  return design.Add(tmp, "top.v", cell.top);
}

constexpr const char* kSoloPlainConfig =
    "config cfg15;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "endconfig\n";

constexpr const char* kInterfaceCellSource =
    "interface bus;\n"
    "  leaf u();\n"
    "endinterface\n"
    "interface leaf;\n"
    "endinterface\n";

constexpr const char* kInterfaceTopSource =
    "module top;\n"
    "  bus x();\n"
    "endmodule\n";

constexpr const char* kInterfaceInnerConfig =
    "config cfg13;\n"
    "  design gateLib.bus;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kInterfaceDelegatingConfig =
    "config cfg14;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.x use work.cfg13:config;\n"
    "endconfig\n";

constexpr const char* kProgramCellSource =
    "program pgm;\n"
    "endprogram\n";

constexpr const char* kProgramTopSource =
    "module top;\n"
    "  pgm x();\n"
    "endmodule\n";

constexpr const char* kProgramInnerConfig =
    "config cfg16;\n"
    "  design gateLib.pgm;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kProgramDelegatingConfig =
    "config cfg17;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.x use work.cfg16:config;\n"
    "endconfig\n";

constexpr const char* kCheckerCellSource =
    "checker chk;\n"
    "endchecker\n";

constexpr const char* kCheckerTopSource =
    "module top;\n"
    "  chk x();\n"
    "endmodule\n";

constexpr const char* kCheckerInnerConfig =
    "config cfg18;\n"
    "  design gateLib.chk;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kCheckerDelegatingConfig =
    "config cfg19;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.x use work.cfg18:config;\n"
    "endconfig\n";

constexpr const char* kDeepCellSource =
    "module leaf;\n"
    "endmodule\n";

constexpr const char* kDeepTopSource =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  sub s();\n"
    "endmodule\n"
    "module sub;\n"
    "  leaf u();\n"
    "endmodule\n";

constexpr const char* kDeepInnerConfig =
    "config cfg20;\n"
    "  design rtlLib.mid;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

constexpr const char* kDeepDelegatingConfig =
    "config cfg21;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.m1 use work.cfg20:config;\n"
    "endconfig\n";

TEST(ConfigHierarchicalConfigExample, DelegatedDesignStatementBindsInterface) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"bus", kInterfaceCellSource, kInterfaceTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = Both(kInterfaceInnerConfig, kInterfaceDelegatingConfig);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg14");
  auto* bound = CellAt(elaborated, "x");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "gateLib");
  auto* inside = CellAt(elaborated, "x.u");
  ASSERT_NE(inside, nullptr);
  EXPECT_EQ(inside->name, "leaf");
  EXPECT_EQ(inside->library, "gateLib");
}

TEST(ConfigHierarchicalConfigExample, WithoutDelegationTheInterfaceIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"bus", kInterfaceCellSource, kInterfaceTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = kSoloPlainConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg15");
  ASSERT_NE(OnlyTop(elaborated), nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "bus", "gateLib"));
  EXPECT_EQ(CellAt(elaborated, "x"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'bus': the configuration's default library "
                    "list (rtlLib) holds no cell 'bus' for instance 'top.x'",
                    2, "33.4.1.5"));
}

TEST(ConfigHierarchicalConfigExample, DelegatedDesignStatementBindsProgram) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"pgm", kProgramCellSource, kProgramTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = Both(kProgramInnerConfig, kProgramDelegatingConfig);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg17");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* bound = CellAt(elaborated, "x");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigHierarchicalConfigExample, WithoutDelegationTheProgramIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"pgm", kProgramCellSource, kProgramTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = kSoloPlainConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg15");
  ASSERT_NE(OnlyTop(elaborated), nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "pgm", "gateLib"));
  EXPECT_EQ(CellAt(elaborated, "x"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'pgm': the configuration's default library "
                    "list (rtlLib) holds no cell 'pgm' for instance 'top.x'",
                    2, "33.4.1.5"));
}

TEST(ConfigHierarchicalConfigExample, DelegatedDesignStatementBindsChecker) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"chk", kCheckerCellSource, kCheckerTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = Both(kCheckerInnerConfig, kCheckerDelegatingConfig);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg19");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* bound = CellAt(elaborated, "x");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigHierarchicalConfigExample, WithoutDelegationTheCheckerIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"chk", kCheckerCellSource, kCheckerTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = kSoloPlainConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg15");
  ASSERT_NE(OnlyTop(elaborated), nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "chk", "gateLib"));
  EXPECT_EQ(CellAt(elaborated, "x"), nullptr);
  EXPECT_TRUE(
      ReportedError(design.diag.Diagnostics(),
                    "unknown module 'chk': the configuration's default library "
                    "list (rtlLib) holds no cell 'chk' for instance 'top.x'",
                    2, "33.4.1.5"));
}

TEST(ConfigHierarchicalConfigExample, DelegatedRulesReachBeyondTheFirstLevel) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"leaf", kDeepCellSource, kDeepTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = Both(kDeepInnerConfig, kDeepDelegatingConfig);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg21");
  ASSERT_FALSE(design.diag.HasErrors());
  auto* middle = CellAt(elaborated, "m1.s");
  ASSERT_NE(middle, nullptr);
  EXPECT_EQ(middle->library, "rtlLib");
  auto* bound = CellAt(elaborated, "m1.s.u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "leaf");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigHierarchicalConfigExample, WithoutDelegationTheDeepCellIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  DelegatedCell cell{"leaf", kDeepCellSource, kDeepTopSource};
  ASSERT_TRUE(BuildSoloCellDesign(tmp, design, cell));

  auto config = kSoloPlainConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg15");
  ASSERT_TRUE(DesignHoldsCell(design.unit, "leaf", "gateLib"));
  auto* middle = CellAt(elaborated, "m1.s");
  ASSERT_NE(middle, nullptr);
  EXPECT_EQ(CellAt(elaborated, "m1.s.u"), nullptr);
  EXPECT_TRUE(ReportedError(
      design.diag.Diagnostics(),
      "unknown module 'leaf': the configuration's default library list "
      "(rtlLib) holds no cell 'leaf' for instance 'top.m1.s.u'",
      8, "33.4.1.5"));
}

std::string LibraryUnderConfigs(const std::string& configs,
                                std::string_view config_name,
                                std::string_view path) {
  ScratchDir tmp;
  LibraryDesign design;
  if (!BuildExampleDesign(tmp, design)) return {};
  auto* elaborated = ElaborateNamedConfig(tmp, design, configs, config_name);
  auto* bound = CellAt(elaborated, path);
  return bound == nullptr ? std::string() : std::string(bound->library);
}

TEST(ConfigHierarchicalConfigExample, DelegatedCellClauseListBindsDescendants) {
  const std::string kConfigs =
      "config cfg13;\n"
      "  design aLib.adder;\n"
      "  default liblist gateLib aLib;\n"
      "  cell m liblist rtlLib;\n"
      "endconfig\n"
      "config cfg14;\n"
      "  design rtlLib.top;\n"
      "  default liblist aLib rtlLib;\n"
      "  instance top.a2 use work.cfg13:config;\n"
      "endconfig\n";
  EXPECT_EQ(LibraryUnderConfigs(kConfigs, "cfg14", "a2.f2"), "rtlLib");
}

TEST(ConfigHierarchicalConfigExample, NestedDelegationIsFollowed) {
  const std::string kConfigs =
      "config cfg15;\n"
      "  design gateLib.m;\n"
      "endconfig\n"
      "config cfg16;\n"
      "  design aLib.adder;\n"
      "  default liblist aLib;\n"
      "  instance adder.f1 use work.cfg15:config;\n"
      "endconfig\n"
      "config cfg17;\n"
      "  design rtlLib.top;\n"
      "  default liblist aLib rtlLib;\n"
      "  instance top.a2 use work.cfg16:config;\n"
      "endconfig\n";
  EXPECT_EQ(LibraryUnderConfigs(kConfigs, "cfg17", "a2.f1"), "gateLib");
}

TEST(ConfigHierarchicalConfigExample, DelegatedCellClauseUsingAConfigBinds) {
  const std::string kConfigs =
      "config cfg18;\n"
      "  design gateLib.m;\n"
      "endconfig\n"
      "config cfg19;\n"
      "  design aLib.adder;\n"
      "  default liblist aLib;\n"
      "  cell m use work.cfg18:config;\n"
      "endconfig\n"
      "config cfg20;\n"
      "  design rtlLib.top;\n"
      "  default liblist aLib rtlLib;\n"
      "  instance top.a2 use work.cfg19:config;\n"
      "endconfig\n";
  EXPECT_EQ(LibraryUnderConfigs(kConfigs, "cfg20", "a2.f2"), "gateLib");
}

TEST(ConfigHierarchicalConfigExample, EnclosingRulesStayOutOfTheSubtree) {
  const std::string kConfigs =
      "config cfg21;\n"
      "  design aLib.adder;\n"
      "endconfig\n"
      "config cfg22;\n"
      "  design rtlLib.top;\n"
      "  default liblist aLib rtlLib;\n"
      "  cell m use gateLib.m;\n"
      "  instance top.a2 use work.cfg21:config;\n"
      "endconfig\n";
  EXPECT_EQ(LibraryUnderConfigs(kConfigs, "cfg22", "a2.f1"), "aLib");
}

}  // namespace
