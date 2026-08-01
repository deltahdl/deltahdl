// Tests for IEEE 1800-2023 §33.2.2 "Basic configuration elements". The
// subclause reads the three statements a configuration is built from and says
// what each one settles:
//
//   - The design statement names the top-level cell of the design and, through
//     the library qualifying that name, the source description that cell is
//     taken from.
//   - The default statement, paired with a library list, settles the binding of
//     every subinstance no more specific clause reaches. Where one library
//     holds the whole design, that one clause is enough to bind all of it.
//   - The instance statement settles the binding of the one instance it names,
//     overriding for that instance what the default clause would otherwise
//     have decided.
//
// Each of these is a rule about which cell an instance binds to, so every test
// writes the configuration as real source, has the cells it selects among live
// in real libraries, and reads the verdict off the elaborated hierarchy.
//
// What the rules consume comes from this pass's dependencies. §33.2.1 supplies
// the library.cell notation the design statement and the selection clauses are
// written in -- every configuration below is written in that notation -- and
// §33.3 supplies the libraries themselves: a library is a collection of cells,
// and a cell is a design element written into it under its own name. A test
// therefore places like-named cells in different libraries and then names one
// of those libraries, which is the only thing that can decide between them.
//
// Libraries reach these tests two ways. Most tests declare their cells in one
// source and assign each its library directly, because one compilation unit is
// mapped to one library and cells of one name in two libraries cannot be
// written any other way in a single source. The tests of the closing section
// take the other route end to end: several source files on disk, a real
// library map naming a library per file, and the mapping machinery of §33.3
// writing each file's cells into the library its path matched -- so nothing
// about the libraries those tests name was assigned by the test itself.
//
// The decoy cell of each pair is declared first throughout, so a binding that
// ignored the library named by the clause under test would fall to the
// first-declared copy and the expected library would never come out.
#include <string>
#include <string_view>
#include <vector>

#include "fixture_config_unit.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"

using namespace delta;

namespace {

// The cell bound to the instance named `inst_name` directly under the design's
// one top module, or nullptr when the design did not come out with that shape.
// Returning nullptr leaves the caller's ASSERT to report it rather than walking
// a hierarchy that is not there.
RtlirModule* BoundChild(RtlirDesign* design, std::string_view inst_name) {
  auto* top = SoleTopModule(design);
  if (top == nullptr) return nullptr;
  for (const auto& inst : top->children) {
    if (inst.inst_name == inst_name) return inst.resolved;
  }
  return nullptr;
}

// The cell bound to the instance `leaf_inst` held by the instance `mid_inst` of
// the design's one top module, or nullptr when no such instance was bound.
RtlirModule* BoundLeafOf(RtlirDesign* design, std::string_view mid_inst,
                         std::string_view leaf_inst) {
  auto* mid = BoundChild(design, mid_inst);
  if (mid == nullptr) return nullptr;
  for (const auto& inst : mid->children) {
    if (inst.inst_name == leaf_inst) return inst.resolved;
  }
  return nullptr;
}

// A top cell holding two instances of `adder`, of which two libraries each hold
// a copy: a gate-level description and an RTL one, in that declaration order.
// The top itself lives in a third library, so nothing the top carries can
// decide which adder an instance binds -- only the library list a clause names
// can. The libraries are gateLib, rtlLib and topLib in declaration order.
constexpr const char* kTwoAdderCells =
    "module adder; endmodule\n"
    "module adder; endmodule\n"
    "module top; adder a1(); adder a2(); endmodule\n";

// A configuration leaving both adder instances to its default clause.
constexpr const char* kDefaultOnlyConfig =
    "config cfg;\n"
    "  design topLib.top;\n"
    "  default liblist rtlLib;\n"
    "endconfig\n";

// The same, with an instance statement naming one of the two instances.
constexpr const char* kInstanceNamesA2Config =
    "config cfg;\n"
    "  design topLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.a2 liblist gateLib;\n"
    "endconfig\n";

// The same, with the instance statement naming a path the design does not hold.
constexpr const char* kInstanceNamesA3Config =
    "config cfg;\n"
    "  design topLib.top;\n"
    "  default liblist rtlLib;\n"
    "  instance top.a3 liblist gateLib;\n"
    "endconfig\n";

// Elaborates the two-adder cells under `config_body`, placing each cell in its
// library, and returns the elaborated design.
RtlirDesign* ElaborateAdderDesign(ConfigUnit& u, const char* config_body) {
  std::string src = kTwoAdderCells;
  src += config_body;
  if (!u.Parse(src)) return nullptr;
  u.PlaceModulesInLibraries({"gateLib", "rtlLib", "topLib"});
  return u.ElaborateConfig(0);
}

// The named library is where the cell has to be: a copy of the name held by
// some other library is not the description the statement asked for. A design
// statement naming a library that holds no such cell therefore names no top at
// all, and the configuration cannot be elaborated.
TEST(ConfigBasicElements, DesignStatementRejectsCellMissingFromNamedLibrary) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "config cfg;\n"
              "  design rtlLib.top;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"gateLib"});
  EXPECT_EQ(u.ElaborateConfig(0), nullptr);
  EXPECT_TRUE(u.diag.HasErrors());
}

// A design statement may name more than one top cell, and each name carries its
// own library. Both names are held by both libraries here, so each top can only
// have come from the library its own name was qualified by.
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

// The other form the notation takes: a design cell written with no library
// qualifier is qualified by the library holding the configuration itself, and
// the top is taken from that library the same way. The configuration is placed
// in rtlLib, so rtlLib's copy of `top` is the one the design gets.
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

// What a library holds is a design element of whatever kind the language
// declares, so the cell a design statement takes from a library need not be a
// module. Both libraries here hold a `dut`: gateLib's is a module and rtlLib's
// is a program. Naming rtlLib takes the program, which is a cell the name on
// its own would not have reached, the module answering to it first.
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

// §33.2.2: the default statement and its library list settle every subinstance
// of the top. Both instances of `adder` are left to it and both take the RTL
// description the list names, which is what makes a default clause on its own
// enough to bind a design held entirely by one library.
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

// Subinstances are not only the top's own children: the clause reaches on down
// the hierarchy. `mid` is taken from midLib, so the library its child is bound
// out of is settled by the default library list rather than by anything `mid`
// itself carries, and rtlLib's leaf is taken over gateLib's.
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

// The library list is where the description has to be found. With the
// gate-level adder the only cell of that name anywhere and the default clause
// naming rtlLib, the subinstance is left with no source description and nothing
// is bound to it.
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
}

// A subinstance is an instance of whatever design element kind a library holds
// as a cell, so the clause settles an interface instance the same way it
// settles a module one. Both libraries hold a `bus`, and the list names rtlLib.
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

// And a program instance, the other kind a module instantiates. The list names
// rtlLib, so the subinstance takes that library's copy of `pgm` over gateLib's.
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

// The particular instance is the one the statement names and no other. A
// statement naming an instance the design does not hold overrides nothing, and
// both adders stay with the default clause's RTL description.
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

// An instance statement names an instance whatever its depth in the design.
// Naming top.m2.lf moves that one leaf to the gate-level description, while the
// like-named leaf under top.m1, which the statement does not name, stays with
// the default clause.
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

// The instance a statement names is an instance of any cell kind a library
// holds, an interface among them. `top.b2` is moved to gateLib while `top.b1`,
// an instance of the same interface, stays with the default clause.
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

// Elaborates the one configuration the assembled files declare.
RtlirDesign* ElaborateSoleConfig(LibraryDesign& s) {
  Elaborator elab(s.arena, s.diag, s.unit);
  return elab.Elaborate(s.unit->configs[0]);
}

// The cell text the mapped files hold. One adder description is written to a
// file the map sends to the RTL library and an identical one to a file it sends
// to the gate-level library, so the two cells differ in nothing a test could
// have arranged except the library their file names earned them.
constexpr const char* kAdderFile = "module adder; endmodule\n";
constexpr const char* kTopFile =
    "module top; adder a1(); adder a2(); endmodule\n";

// Writes the library map and the source files of the two-adder design, then
// parses them in an order that leaves the gate-level adder first. The
// configuration goes in a file of its own so nothing it names comes from the
// library holding it. Returns false when a file did not parse.
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

// §33.2.2, end to end through §33.3: a design statement says which cell tops
// the design and which library that cell's description is taken from. Two
// files each declare a cell named `top`, and a library map sends one to rtlLib
// and the other to gateLib by file name alone. The statement names rtlLib, so
// the design is topped by the cell out of the file the map put in that library
// rather than by the like-named cell the other file supplied.
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

// End to end through §33.3: the default clause names rtlLib, and the adder
// instance left to it takes the description out of the file the map wrote into
// that library rather than the gate-level file parsed before it.
TEST(ConfigBasicElements, DefaultClauseBindsSubinstanceFromMappedLibrary) {
  ScratchDir tmp;
  LibraryDesign s;
  ASSERT_TRUE(BuildMappedAdderDesign(tmp, s, kDefaultOnlyConfig));
  auto* a1 = BoundChild(ElaborateSoleConfig(s), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "rtlLib");
}

// §33.2.2, end to end through §33.3: an instance statement written beside a
// default clause names gateLib for top.a2, so that instance takes the
// description out of the gate-level file in place of the RTL one the default
// clause would have given it. What the statement overrides is the default rule
// for that one instance: top.a1, which it does not name, still takes the RTL
// description. Both libraries were assigned by the map, not by the test.
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

}  // namespace
