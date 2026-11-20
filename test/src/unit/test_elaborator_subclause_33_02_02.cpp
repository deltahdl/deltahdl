#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "fixture_config_unit.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

RtlirModule* BoundChild(RtlirDesign* design, std::string_view inst_name) {
  auto* top = SoleTopModule(design);
  if (top == nullptr) return nullptr;
  for (const auto& inst : top->children) {
    if (inst.inst_name == inst_name) return inst.resolved;
  }
  return nullptr;
}

RtlirModule* BoundLeafOf(RtlirDesign* design, std::string_view mid_inst,
                         std::string_view leaf_inst) {
  auto* mid = BoundChild(design, mid_inst);
  if (mid == nullptr) return nullptr;
  for (const auto& inst : mid->children) {
    if (inst.inst_name == leaf_inst) return inst.resolved;
  }
  return nullptr;
}

constexpr const char* kTwoAdderCells =
    "module adder; endmodule\n"
    "module adder; endmodule\n"
    "module top; adder a1(); adder a2(); endmodule\n";

constexpr const char* kDefaultOnlyConfig =
    "config cfg;\n"
    "  design topLib.top;\n"
    "  default liblist rtlLib;\n"
    "endconfig\n";

constexpr const char* kInstanceNamesA2Config =
    "config cfg;\n"
    "  design topLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.a2 liblist gateLib;\n"
    "endconfig\n";

constexpr const char* kInstanceNamesA3Config =
    "config cfg;\n"
    "  design topLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.a3 liblist gateLib;\n"
    "endconfig\n";

RtlirDesign* ElaborateAdderDesign(ConfigUnit& u, const char* config_body) {
  std::string src = kTwoAdderCells;
  src += config_body;
  if (!u.Parse(src)) return nullptr;
  u.PlaceModulesInLibraries({"gateLib", "rtlLib", "topLib"});
  return u.ElaborateConfig(0);
}

TEST(ConfigBasicElements, DesignStatementRejectsCellMissingFromNamedLibrary) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "config cfg;\n"
              "  design rtlLib.top;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib"});
  EXPECT_EQ(u.ElaborateConfig(0), nullptr);
  EXPECT_TRUE(ReportedError(
      u.diag.Diagnostics(),
      "config 'cfg' design cell 'top' not found in library 'rtlLib'", 3,
      "33.4.1.1"));
}

TEST(ConfigBasicElements, DesignStatementTakesEachTopFromItsOwnLibrary) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module topa; endmodule\n"
              "module topa; endmodule\n"
              "module topb; endmodule\n"
              "module topb; endmodule\n"
              "config cfg;\n"
              "  design rtlLib.topa gateLib.topb;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib", "rtlLib", "rtlLib", "gateLib"});
  auto* design = u.ElaborateConfig(0);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "topa");
  EXPECT_EQ(design->top_modules[0]->library, "rtlLib");
  EXPECT_EQ(design->top_modules[1]->name, "topb");
  EXPECT_EQ(design->top_modules[1]->library, "gateLib");
}

TEST(ConfigBasicElements, UnqualifiedDesignCellTakesTopFromConfigLibrary) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "module top; endmodule\n"
              "config cfg;\n"
              "  design top;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib", "rtlLib"});
  u.PlaceConfigInLibrary("rtlLib");
  auto* top = SoleTopModule(u.ElaborateConfig(0));
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "rtlLib");
}

TEST(ConfigBasicElements, DesignStatementTakesProgramTopFromNamedLibrary) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module dut; endmodule\n"
              "program dut; endprogram\n"
              "config cfg;\n"
              "  design rtlLib.dut;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib"});
  u.cu->programs[0]->library = "rtlLib";
  auto* top = SoleTopModule(u.ElaborateConfig(0));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->is_program);
  EXPECT_EQ(top->library, "rtlLib");
}

TEST(ConfigBasicElements, DefaultLiblistBindsEverySubinstanceOfTheTop) {
  ConfigUnit u;
  auto* design = ElaborateAdderDesign(u, kDefaultOnlyConfig);
  auto* a1 = BoundChild(design, "a1");
  auto* a2 = BoundChild(design, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a1->library, "rtlLib");
  EXPECT_EQ(a2->library, "rtlLib");
}

TEST(ConfigBasicElements, DefaultLiblistReachesBelowTheTopsOwnChildren) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"
              "module leaf; endmodule\n"
              "module mid; leaf lf(); endmodule\n"
              "module top; mid m(); endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib midLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib", "rtlLib", "midLib", "topLib"});
  auto* design = u.ElaborateConfig(0);
  ExpectChainBindsChildAndLeaf(design, "mid", "midLib", "rtlLib");
}

TEST(ConfigBasicElements, DefaultLiblistLeavesUnlistedSubinstanceUnbound) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module adder; endmodule\n"
              "module top; adder a1(); endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib", "topLib"});
  auto* design = u.ElaborateConfig(0);
  ASSERT_NE(SoleTopModule(design), nullptr);
  EXPECT_EQ(BoundChild(design, "a1"), nullptr);
  EXPECT_TRUE(ReportedError(
      u.diag.Diagnostics(),
      "unknown module 'adder': the configuration's default library list "
      "(rtlLib) holds no cell 'adder' for instance 'top.a1'",
      2, "33.4.1.5"));
}

TEST(ConfigBasicElements, DefaultLiblistSelectsInterfaceSubinstance) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("interface bus; endinterface\n"
              "interface bus; endinterface\n"
              "module top; bus b(); endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"topLib"});
  u.cu->interfaces[0]->library = "gateLib";
  u.cu->interfaces[1]->library = "rtlLib";
  auto* bound = BoundChild(u.ElaborateConfig(0), "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "rtlLib");
}

TEST(ConfigBasicElements, DefaultLiblistSelectsProgramSubinstance) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("program pgm; endprogram\n"
              "program pgm; endprogram\n"
              "module top; pgm p(); endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"topLib"});
  u.cu->programs[0]->library = "gateLib";
  u.cu->programs[1]->library = "rtlLib";
  auto* bound = BoundChild(u.ElaborateConfig(0), "p");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "rtlLib");
}

TEST(ConfigBasicElements, InstanceStatementNamingNoInstanceOverridesNothing) {
  ConfigUnit u;
  auto* design = ElaborateAdderDesign(u, kInstanceNamesA3Config);
  auto* a1 = BoundChild(design, "a1");
  auto* a2 = BoundChild(design, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a1->library, "rtlLib");
  EXPECT_EQ(a2->library, "rtlLib");
}

TEST(ConfigBasicElements, InstanceStatementNamesAnInstanceAtAnyDepth) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"
              "module leaf; endmodule\n"
              "module mid; leaf lf(); endmodule\n"
              "module top; mid m1(); mid m2(); endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib;\n"
              "  instance top.m2.lf liblist gateLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"rtlLib", "gateLib", "rtlLib", "topLib"});
  auto* design = u.ElaborateConfig(0);
  auto* lf1 = BoundLeafOf(design, "m1", "lf");
  auto* lf2 = BoundLeafOf(design, "m2", "lf");
  ASSERT_NE(lf1, nullptr);
  ASSERT_NE(lf2, nullptr);
  EXPECT_EQ(lf1->library, "rtlLib");
  EXPECT_EQ(lf2->library, "gateLib");
}

TEST(ConfigBasicElements, InstanceStatementSelectsInterfaceInstance) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("interface bus; endinterface\n"
              "interface bus; endinterface\n"
              "module top; bus b1(); bus b2(); endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib;\n"
              "  instance top.b2 liblist gateLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"topLib"});
  u.cu->interfaces[0]->library = "rtlLib";
  u.cu->interfaces[1]->library = "gateLib";
  auto* design = u.ElaborateConfig(0);
  auto* b1 = BoundChild(design, "b1");
  auto* b2 = BoundChild(design, "b2");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b1->library, "rtlLib");
  EXPECT_EQ(b2->library, "gateLib");
}

RtlirDesign* ElaborateSoleConfig(LibraryDesign& s) {
  Elaborator elab(s.arena, s.diag, s.unit);
  return elab.Elaborate(s.unit->configs[0]);
}

constexpr const char* kAdderFile = "module adder; endmodule\n";
constexpr const char* kTopFile =
    "module top; adder a1(); adder a2(); endmodule\n";

bool BuildMappedAdderDesign(ScratchDir& tmp, LibraryDesign& s,
                            const std::string& config_body) {
  auto map_file = tmp.Write("lib.map",
                            "library topLib *.sv;\n"
                            "library rtlLib *.v;\n"
                            "library gateLib *.vg;\n");
  if (!s.map.LoadMapFile(map_file)) return false;
  auto gate = tmp.Write("adder.vg", kAdderFile);
  auto rtl = tmp.Write("adder.v", kAdderFile);
  auto top = tmp.Write("top.sv", kTopFile);
  auto cfg = tmp.Write("cfg.sv", config_body);
  return s.AddFile(gate, kAdderFile) && s.AddFile(rtl, kAdderFile) &&
         s.AddFile(top, kTopFile) && s.AddFile(cfg, config_body);
}

TEST(ConfigBasicElements, DesignStatementTakesTopFromMappedLibrary) {
  ScratchDir tmp;
  LibraryDesign s;
  auto map_file = tmp.Write("lib.map",
                            "library rtlLib *.v;\n"
                            "library gateLib *.vg;\n"
                            "library cfgLib *.sv;\n");
  ASSERT_TRUE(s.map.LoadMapFile(map_file));
  const std::string kTopCell = "module top; endmodule\n";
  const std::string kCfgCell =
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "endconfig\n";
  ASSERT_TRUE(s.AddFile(tmp.Write("top.vg", kTopCell), kTopCell));
  ASSERT_TRUE(s.AddFile(tmp.Write("top.v", kTopCell), kTopCell));
  ASSERT_TRUE(s.AddFile(tmp.Write("cfg.sv", kCfgCell), kCfgCell));
  auto* top = SoleTopModule(ElaborateSoleConfig(s));
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "rtlLib");
}

TEST(ConfigBasicElements, DefaultClauseBindsSubinstanceFromMappedLibrary) {
  ScratchDir tmp;
  LibraryDesign s;
  ASSERT_TRUE(BuildMappedAdderDesign(tmp, s, kDefaultOnlyConfig));
  auto* a1 = BoundChild(ElaborateSoleConfig(s), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "rtlLib");
}

TEST(ConfigBasicElements, InstanceClauseBindsItsInstanceFromMappedLibrary) {
  ScratchDir tmp;
  LibraryDesign s;
  ASSERT_TRUE(BuildMappedAdderDesign(tmp, s, kInstanceNamesA2Config));
  auto* design = ElaborateSoleConfig(s);
  auto* a1 = BoundChild(design, "a1");
  auto* a2 = BoundChild(design, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a1->library, "rtlLib");
  EXPECT_EQ(a2->library, "gateLib");
}

TEST(ConfigBasicElements, DefaultLiblistBindsTheSubinstancesOfEveryTop) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"
              "module leaf; endmodule\n"
              "module ta; leaf u(); endmodule\n"
              "module tb; leaf u(); endmodule\n"
              "config cfg;\n"
              "  design topLib.ta topLib.tb;\n"
              "  default liblist rtlLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib", "rtlLib", "topLib", "topLib"});
  auto* design = u.ElaborateConfig(0);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  for (const auto* top : design->top_modules) {
    ASSERT_EQ(top->children.size(), 1u);
    const auto* leaf = top->children[0].resolved;
    ASSERT_NE(leaf, nullptr);
    EXPECT_EQ(leaf->library, "rtlLib");
  }
}

TEST(ConfigBasicElements, InstanceStatementSelectsProgramInstance) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("program pgm; endprogram\n"
              "program pgm; endprogram\n"
              "module top; pgm p1(); pgm p2(); endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib;\n"
              "  instance top.p2 liblist gateLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"topLib"});
  u.cu->programs[0]->library = "rtlLib";
  u.cu->programs[1]->library = "gateLib";
  auto* design = u.ElaborateConfig(0);
  auto* p1 = BoundChild(design, "p1");
  auto* p2 = BoundChild(design, "p2");
  ASSERT_NE(p1, nullptr);
  ASSERT_NE(p2, nullptr);
  EXPECT_TRUE(p2->is_program);
  EXPECT_EQ(p1->library, "rtlLib");
  EXPECT_EQ(p2->library, "gateLib");
}

std::string_view UdpLibraryOf(const RtlirModule* mod, std::string_view inst) {
  for (const auto& udp : mod->udp_insts) {
    if (udp.name == inst && udp.decl != nullptr) return udp.decl->library;
  }
  return "";
}

TEST(ConfigBasicElements, InstanceStatementSelectsPrimitiveInstance) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("primitive u_and(output o, input a);\n"
              "  table 0 : 0 ; 1 : 1 ; endtable\n"
              "endprimitive\n"
              "primitive u_and(output o, input a);\n"
              "  table 0 : 1 ; 1 : 0 ; endtable\n"
              "endprimitive\n"
              "module top; wire o1, o2, a; u_and u1(o1, a); u_and u2(o2, a);\n"
              "endmodule\n"
              "config cfg;\n"
              "  design topLib.top;\n"
              "  default liblist rtlLib;\n"
              "  instance top.u2 liblist gateLib;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"topLib"});
  u.cu->udps[0]->library = "rtlLib";
  u.cu->udps[1]->library = "gateLib";
  auto* top = SoleTopModule(u.ElaborateConfig(0));
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(UdpLibraryOf(top, "u1"), "rtlLib");
  EXPECT_EQ(UdpLibraryOf(top, "u2"), "gateLib");
}

}  // namespace
