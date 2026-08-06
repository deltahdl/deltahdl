// Tests for IEEE 1800-2023 §33.6.5 "Using hierarchical config".
//
// The subclause takes a configuration already written for a lower cell of the
// §33.6 design and reuses it inside a configuration written for the whole
// design. The clause that does it is an instance selection whose expansion
// names a configuration rather than a cell -- the ':config' extension says so
// outright -- and it hands that configuration the binding of the one instance
// it selects together with everything hanging below it.
//
// Three things follow, and the tests below are grouped by them. The named
// configuration's design statement is what binds the selected instance itself,
// so that instance takes the cell the statement names however the enclosing
// configuration's own default clause would have answered. The rest of the
// named configuration -- its default clause and its own instance clauses --
// binds the descendants of the selected instance, and nothing else in the
// design. And an instance path written inside the named configuration counts
// down from that configuration's own design cell rather than from the
// enclosing design's top cell, so the enclosing clause is what says which
// subhierarchy the path is read against.
//
// The rule is applied at the elaborator stage. A delegating clause is
// recognised through UseClauseNamesConfig and expanded by
// CollectConfigDelegationOverrides (src/elaborator/elaborator.cpp), which
// records the inner configuration's design cell as an instance use override
// and translates the inner rules through CollectInnerConfigLiblistOverrides;
// the InnerPathUnderTop test inside CollectInnerConfigInstanceOverride is the
// relative-path reading, and it is what rewrites an inner path onto the outer
// hierarchy. Elaborator::FindModule consults the use override ahead of every
// library list (src/elaborator/elaborator_resolve.cpp), which is how the inner
// design statement outranks both default clauses at the selected instance, and
// InstanceLiblistForPath there takes the longest matching path, which is how
// an inner instance clause outranks the inner default clause below it. A path
// that is not written against the inner configuration's own design cell is
// reported by ValidateConfigInstanceClauses
// (src/elaborator/elaborator_validate_config.cpp).
//
// What the rule consumes comes from this pass's dependencies: §33.6.2's
// default clause, which both configurations carry and whose answer the
// delegation displaces over one subhierarchy, and §33.6.4's instance clause
// paired with a library list, which is the form the inner configuration's own
// rule takes and the form the outer selection takes before its expansion. The
// libraries themselves come from §33.6.1's map. Every test therefore writes
// the §33.6 library map and source files to disk, loads the map, parses each
// file and tags it through the map, installs the map's declaration order on
// the elaborator, and only then elaborates a configuration; no test writes a
// library onto a cell or states a search order of its own. Each claim about a
// binding the delegation produced is paired with the same design elaborated
// under the same enclosing configuration with the delegating clause struck
// out, since a binding that would have landed there anyway shows nothing.
//
// A cell is a design element of any kind a library holds, so the closing pair
// reads the same two claims over an interface: the delegated configuration's
// design statement names one, and the cell inside it is bound by that
// configuration's default clause.

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// The library map of §33.6: rtlLib is declared first, aLib second, gateLib
// last. Both the aLib and the gateLib specification cover adder.vg, and only
// gateLib's names that file outright, which is what leaves the gate-level
// descriptions in gateLib and the RTL ones in aLib.
constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

// top.v: the cell topping the design instantiates the adder twice, so a
// configuration handed one of them has a sibling to leave alone. Its cell
// named m is the only m that reaches rtlLib.
constexpr const char* kTopSource =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// adder.v and adder.vg: the RTL and the gate-level description of the same two
// cells. One text stands for both files, so the two differ in nothing a test
// could have arranged except the library their file names earned them, and the
// adder each describes instantiates m twice -- f1 and f2, the two descendants
// the configuration written for the adder alone tells apart.
constexpr const char* kAdderSource =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// The configuration of §33.6.5 written for the adder alone. Its design
// statement tops it out at a cell that is not the design's top cell, its
// default clause takes the gate-level m, and its instance clause -- a path
// counted down from its own design cell -- takes the RTL m for f1.
constexpr const char* kInnerConfig =
    "config cfg5;\n"
    "  design aLib.adder;\n"
    "  default liblist gateLib aLib;\n"
    "  instance adder.f1 liblist rtlLib;\n"
    "endconfig\n";

// The configuration of §33.6.5 written for the whole design. Its own default
// clause names neither the gate-level library nor anything that answers rtlLib
// for a cell named m, so every binding beneath the second adder that the tests
// below claim for the delegation is one this clause could not have produced.
constexpr const char* kDelegatingConfig =
    "config cfg6;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 use work.cfg5:config;\n"
    "endconfig\n";

// Its companion: the same enclosing configuration with the delegating clause
// struck out, which is the answer the delegation displaces.
constexpr const char* kPlainConfig =
    "config cfg7;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

// The same delegation under an enclosing default clause that takes the
// gate-level description of every cell that has one. The delegated
// configuration's own default clause lists that library first as well, so the
// adder bound at the selected instance can have come from neither list: the
// only rule in either configuration that answers aLib for the instance itself
// is the design statement of the delegated configuration.
constexpr const char* kGatePreferringDelegating =
    "config cfg8;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a2 use work.cfg5:config;\n"
    "endconfig\n";

// Its companion, which is what those library lists answer with nothing
// delegated.
constexpr const char* kGatePreferringPlain =
    "config cfg9;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

// The nearest input the delegating clause has to turn away: a clause naming a
// configuration the compilation unit does not hold. The ':config' extension
// settles that a configuration is what was meant, so the name reaching none is
// reported rather than read as a cell.
constexpr const char* kDelegatingToUnknownConfig =
    "config cfg10;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 use work.nosuch:config;\n"
    "endconfig\n";

// The rejecting side of the relative-path reading: a configuration written for
// the adder whose instance clause spells the path the enclosing design would
// have used. Counted down from this configuration's own design cell the path
// starts at a cell it never names, so the clause selects nothing at all.
constexpr const char* kOuterRelativeInnerConfig =
    "config cfg11;\n"
    "  design aLib.adder;\n"
    "  default liblist gateLib aLib;\n"
    "  instance top.a2.f1 liblist rtlLib;\n"
    "endconfig\n";

// The enclosing configuration that delegates to it, so the path above is read
// over exactly the subhierarchy that would have made it fit had paths been
// counted from the enclosing design's top cell.
constexpr const char* kDelegatingToOuterRelative =
    "config cfg12;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 use work.cfg11:config;\n"
    "endconfig\n";

// Writes the §33.6 library map and the three source descriptions, loading the
// map before any of them so every cell is tagged through it, and parsing the
// RTL description first and the topping file last. An implementation binding
// whichever description it parsed first would answer aLib everywhere, which
// each pairing below rules out: the same files under a configuration carrying
// no delegating clause answer something else at every binding the delegation
// is claimed to have decided. Returns false when a file does not parse.
bool BuildExampleDesign(ScratchDir& tmp, LibraryDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, "adder.v", kAdderSource)) return false;
  if (!design.Add(tmp, "adder.vg", kAdderSource)) return false;
  return design.Add(tmp, "top.v", kTopSource);
}

// Two configurations written into one file, which is what a delegating clause
// needs: it reaches the configuration it names through the compilation unit
// both were parsed into.
std::string Both(const char* first, const char* second) {
  return std::string(first) + second;
}

// The premise the subclause starts from: the configuration written for the
// adder alone, elaborated in its own right. Its design statement tops the
// design out at a cell the §33.6 design instantiates rather than at that
// design's own top cell, its instance clause takes the RTL m for f1, and its
// default clause takes the gate-level m for f2. This is what the delegating
// clauses below reuse, and this is what it does before any of them names it.
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

// The delegated configuration's design statement is what binds the instance
// the delegating clause selects. Both library lists in force here take the
// gate-level adder, and the design statement of the delegated configuration
// names the RTL one, so the cell bound at the second adder came from that
// statement and from nothing else.
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

// Its companion: the same design under the same enclosing default clause with
// the delegating clause struck out takes the gate-level adder at that very
// instance. The pair is what makes the claim above about the delegated design
// statement rather than about a binding the enclosing rules gave anyway.
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

// The delegated configuration's default clause binds the descendants of the
// selected instance. It names the gate-level library, which the enclosing
// configuration's own default clause leaves out entirely, and the second cell
// beneath the second adder comes from there.
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

// The delegated configuration's own instance clause binds the descendant its
// path selects, and it outranks that configuration's default clause there. The
// RTL m is what no default clause in either configuration would have reached:
// the enclosing one lists aLib first and the delegated one gateLib first.
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

// The companion of both claims above: with the delegating clause struck out,
// every cell beneath the second adder follows the enclosing default clause and
// comes from aLib. Neither the gate-level answer at f2 nor the RTL answer at
// f1 is where this design lands on its own.
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

// What the delegating clause hands over is one instance with its descendants,
// so the sibling instance and everything below it are left to the enclosing
// configuration: read in the very elaboration that gave the second adder its
// own rules, the first adder and both cells beneath it follow the enclosing
// default clause, and the design still tops out where the enclosing design
// statement put it.
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

// A path inside the delegated configuration is counted down from that
// configuration's own design cell, so a path spelled against the enclosing
// design is not that path read one level up: it starts at a cell the delegated
// configuration never tops out at, and it is reported.
TEST(ConfigHierarchicalConfigExample, DelegatedPathAgainstOuterTopIsReported) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto config = Both(kOuterRelativeInnerConfig, kDelegatingToOuterRelative);
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg12");
  EXPECT_NE(elaborated, nullptr);
  EXPECT_TRUE(design.diag.HasErrors());
}

// And it selects nothing: the cell that path would have named had paths been
// counted from the enclosing design's top comes from the delegated
// configuration's default clause instead, which is the gate-level m. The
// clause names the RTL library, and no binding in the design answers rtlLib.
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
}

// The nearest input the delegating clause has to turn away: the extension says
// a configuration is what the name means, the compilation unit holds no
// configuration of that name, and the clause is reported rather than read as a
// use clause naming a cell.
TEST(ConfigHierarchicalConfigExample, DelegationToAnUnknownConfigIsReported) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto config = kDelegatingToUnknownConfig;
  auto* elaborated = ElaborateNamedConfig(tmp, design, config, "cfg10");
  EXPECT_NE(elaborated, nullptr);
  EXPECT_TRUE(design.diag.HasErrors());
}

// One cell described in a file of its own, for the pairs below that vary the
// kind of design element the delegated design statement names and the depth
// the delegated rules have to reach. `base` names the file -- base.vg, which
// the map sends to gateLib -- `text` is the description written into it, and
// `top` is the topping file, describing the cell that instantiates it.
struct DelegatedCell {
  std::string base;
  const char* text;
  const char* top;
};

// Writes a map holding the topping file in rtlLib and `cell.base`.vg in
// gateLib, loads it, and parses both files through it. The enclosing
// configurations below name rtlLib alone, so the only description of the cell
// under test sits in a library nothing but the delegated configuration
// reaches. Returns false when the map does not load or a file does not parse.
bool BuildSoloCellDesign(ScratchDir& tmp, LibraryDesign& design,
                         const DelegatedCell& cell) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library gateLib " + cell.base + ".vg;\n";
  auto map_path = tmp.Write("lib.map", map_text);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, cell.base + ".vg", cell.text)) return false;
  return design.Add(tmp, "top.v", cell.top);
}

// The companion of every delegating configuration below: the same enclosing
// configuration with the clause struck out. Its default clause names only the
// library holding the topping file, so a cell described anywhere else is out
// of reach without the delegation.
constexpr const char* kSoloPlainConfig =
    "config cfg15;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "endconfig\n";

// The interface, the first kind of cell read here that is not a module, with a
// cell of its own inside it so the same pair reads the delegated default
// clause reaching a descendant.
constexpr const char* kInterfaceCellSource =
    "interface bus;\n"
    "  leaf u();\n"
    "endinterface\n"
    "module leaf;\n"
    "endmodule\n";

constexpr const char* kInterfaceTopSource =
    "module top;\n"
    "  bus x();\n"
    "endmodule\n";

// The delegated configuration, whose design statement names the interface and
// whose default clause is what reaches the cell inside it.
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

// The program, the next kind of design element a library holds as a cell.
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

// The checker, the remaining kind an instantiation reaches by name.
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

// A cell described three levels below the topping cell, for the pair reading
// how far down the delegated rules run.
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

// The delegated configuration is written for the cell in the middle, so the
// leaf sits two levels below the instance the enclosing clause hands over and
// one level below the cell that instance's own descendants start at.
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

// A cell is a design element of any kind, so a delegated design statement
// binds the selected instance whether it names a module or an interface, and
// the delegated default clause reaches the cell inside it just the same. Both
// come from the library the enclosing default clause leaves out.
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

// Its companion: with the delegating clause struck out the enclosing default
// clause is all there is, it leaves out the only library holding the
// interface, and the instance binds nothing.
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
}

// And for a program: the design statement of the delegated configuration names
// one, and the instance the enclosing clause selects is bound to it out of the
// library the enclosing default clause leaves out.
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

// Its companion.
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
}

// And for a checker, the remaining kind a design statement can name.
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

// Its companion.
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
}

// What the delegated configuration binds is every descendant of the instance
// handed to it, not that instance's children: the leaf two levels below it
// comes from the library only the delegated default clause names, while the
// cell between them comes from the library both configurations list. The
// enclosing clause names the grandparent of the instance that binds the leaf.
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

// Its companion, two levels down: with the delegating clause struck out the
// cell between them still binds, and the leaf below it does not.
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
}

}  // namespace
