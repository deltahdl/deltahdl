// Tests for IEEE 1800-2023 §33.6.3 "Using cell clause".
//
// The subclause reads a cell selection clause paired with a use expansion out
// over the design of §33.6 and states two things about it. The clause selects
// every cell of the name it gives -- all of them, not one instance of one of
// them -- and it binds each of those cells outright to the one library.cell the
// use expansion names. Binding outright is the whole of the difference from the
// clauses around it: the configuration these tests read carries a default
// clause listing two libraries and names a cell in a third, and the cell
// arrives from that third library all the same, because the clause says where
// the description comes from instead of asking for a search a library list
// could exclude it from. What the clause does not name it does not touch, so
// the cell the configuration leaves unmentioned still comes from wherever the
// default clause's list sends the search.
//
// The rule is applied at the elaborator stage. A cell clause's use expansion
// reaches the elaborator through Elaborator::CollectConfigCellClauseOverrides
// (src/elaborator/elaborator.cpp) and decides the binding in
// Elaborator::ResolveCellUseOverride, which Elaborator::FindModule consults
// ahead of every library list it would otherwise filter against
// (src/elaborator/elaborator_resolve.cpp). A primitive is settled on the same
// terms at the head of Elaborator::FindUdpByName
// (src/elaborator/elaborator_items_udp.cpp), which reads the clause through
// CellUseOverrideApplies and FindUdpInLibrary
// (src/elaborator/elaborator_helpers.h).
//
// What the rule consumes comes from this pass's dependencies. §33.6.1 settles
// what a design binds when no configuration is in force and §33.6.2 what a
// default clause's list binds instead, and it is the second of those answers
// this clause has to overturn: under the §33.6 library map the list
// `aLib rtlLib` binds aLib.m at every cell named m, so a cell clause naming
// gateLib.m has to move four bindings that both the map's declaration order and
// the default clause had already settled elsewhere. Every test therefore writes
// the §33.6 library map and source files to disk, loads the map, parses each
// file and tags it through the map, installs the map's own declaration order on
// the elaborator, and only then elaborates a configuration. No test states a
// library or a search order of its own, and every claim about a binding the
// clause moved is read against the same design elaborated without the clause,
// since a binding that would have landed there anyway shows nothing.
//
// A cell is a design element of any kind a library holds, so a clause selecting
// all cells of a name is read over a module, an interface, a program, a checker
// and a primitive. The module case is the §33.6 design itself; the other four
// put the only description of the instantiated cell in a library the default
// clause leaves out, so what the instance binds is decided by the cell clause
// alone, and each is paired with the same design under a configuration carrying
// no cell clause at all.

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The library map of §33.6: rtlLib is declared first, aLib second, gateLib
// last. Both the aLib and the gateLib specification cover adder.vg, and the
// gateLib specification names that file outright while the aLib one reaches it
// only through a wildcard, which is what leaves the gate-level descriptions in
// gateLib and the RTL ones in aLib.
constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

// top.v: the cell topping the design instantiates the adder twice, so a claim
// made about every cell of a name has more than one parent to hold under. The
// file also describes a cell named m, and that description is the only m that
// reaches rtlLib.
constexpr const char* kTopSource =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// adder.v and adder.vg: the RTL and the gate-level description of the same two
// cells. One text stands for both files, so the two descriptions differ in
// nothing a test could have arranged except the library their file names earned
// them, and the adder each file describes instantiates m twice.
constexpr const char* kAdderSource =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// The configuration of §33.6.3. Its default clause lists aLib and rtlLib, so
// the adder is looked for in the RTL library, and its cell clause names the
// gate-level description of m in gateLib -- a library that list does not carry.
constexpr const char* kConfigWithCellClause =
    "config cfg3;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  cell m use gateLib.m;\n"
    "endconfig\n";

// The same configuration with the cell clause struck out, which is the answer
// the clause has to overturn: with the list alone, m comes from the first
// listed library holding one.
constexpr const char* kConfigWithoutCellClause =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

// The nearest input the binding has to turn away: the same clause naming a cell
// gateLib does not hold. The clause still selects every cell named m, so what
// those cells bind says whether a binding naming nothing falls back to the list
// or leaves the name unanswered.
constexpr const char* kConfigMissingTarget =
    "config cfg7;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  cell m use gateLib.nosuch;\n"
    "endconfig\n";

// Writes the §33.6 library map and the three source descriptions and parses
// them with the gate-level file first and the topping file last. An
// implementation binding the description it parsed first would answer gateLib
// throughout, so the parse order cannot be what produces an expectation of
// gateLib below. Returns false when the map does not load or a file does not
// parse.
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

// The libraries the four cells named m in the §33.6 design bound out of. The
// design instantiates the adder twice and each adder instantiates m twice, so a
// clause selecting all cells of a name has four bindings to answer for and they
// sit under two different parents; reading all four at once is what a claim
// about every cell of a name, rather than about one instance of one, comes to.
std::vector<std::string> LibrariesBindingM(RtlirModule* top) {
  return LibrariesBoundBeneath(top, {"a1", "a2"}, {"f1", "f2"});
}

// The clause selects every cell of the name it gives and binds each of them to
// the cell it names, so all four cells named m come from gateLib. Two other
// libraries hold an m -- aLib, which the default clause lists first, and
// rtlLib, which the library map declares first -- and neither supplies any of
// the four, so the clause is what settled every one of them.
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

// The answer the clause overturns, read off the same design under the same
// default clause with the cell clause struck out: the list is searched, aLib is
// listed ahead of rtlLib and holds an m, and all four cells named m bind aLib.
// The pair is what shows the cell clause moved them, since a binding the list
// would have produced anyway proves nothing about a clause.
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

// What the clause selects is a name, so a cell of any other name is left to the
// clauses around it. The configuration selects m alone; the adder is bound out
// of the RTL library its default clause lists first even though gateLib holds
// an adder of its own and the cell clause has just named gateLib, and the
// design still tops out where the design statement put it.
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

// The nearest input the binding has to turn away: the clause selects every cell
// named m and binds it to a cell gateLib does not hold. A binding names its
// description rather than opening a search, so there is no list left to fall
// back to -- the selected cells are reported and left unbound rather than
// filled in from the aLib m the default clause would otherwise have taken.
TEST(ConfigCellClauseExample, UseExpansionNamingNoCellLeavesTheCellsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  ASSERT_TRUE(DesignHoldsCell(design.unit, "m", "aLib"));
  ASSERT_FALSE(DesignHoldsCell(design.unit, "nosuch", "gateLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, design, kConfigMissingTarget));
  ASSERT_NE(top, nullptr);
  // f1, the first of the two instances of m kAdderSource writes, on its second
  // line.
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), "unknown module 'm'", 2,
                            "23.3.2"));
  std::vector<std::string> expected(4, "");
  EXPECT_EQ(LibrariesBindingM(top), expected);
}

// One cell described in a file of its own, for the tests that vary the kind of
// design element a library holds. `base` names the file -- base.vg, which the
// map below sends to gateLib -- `text` is the description written into it, and
// `top` describes the cell instantiating it once, from the file the map sends
// to rtlLib.
struct SoloCell {
  std::string base;
  std::string text;
  std::string top;
};

// The cell clause of §33.6.3 written for `name`: it selects every cell of that
// name and binds each to the like-named cell gateLib holds.
std::string CellUseGateLib(std::string_view name) {
  std::string clause = "  cell ";
  clause += name;
  clause += " use gateLib.";
  clause += name;
  clause += ";\n";
  return clause;
}

// The configuration the tests below elaborate. It names the topping cell in
// rtlLib, so the design root is settled by the design statement, and its
// default clause names rtlLib alone -- leaving out the library holding the only
// description of the instantiated cell, so a search reaches nothing there.
// `cell_clause` is either the clause naming that library outright or nothing at
// all, which is the whole of what differs between a pair of tests.
std::string SoloCellConfig(std::string_view cell_clause) {
  std::string text = "config cfg;\n";
  text += "  design rtlLib.top;\n";
  text += "  default liblist rtlLib;\n";
  text += cell_clause;
  text += "endconfig\n";
  return text;
}

// Writes a map holding the topping file in rtlLib and `cell.base`.vg in
// gateLib, parses both files, and elaborates the configuration `cell_clause`
// completes. Returns the design, or nullptr when the map does not load or a
// file does not parse.
RtlirDesign* ElaborateSoloCell(ScratchDir& tmp, LibraryDesign& design,
                               const SoloCell& cell,
                               std::string_view cell_clause) {
  if (!BuildTwoLibraryDesign(tmp, design, cell.base, cell.text, cell.top)) {
    return nullptr;
  }
  return ElaborateConfigText(tmp, design, SoloCellConfig(cell_clause));
}

// The configuration body carrying no cell clause, for the companion of each
// pair below.
constexpr const char* kNoCellClause = "";

// The interface described in the file the map sends to gateLib, and the cell
// instantiating it.
constexpr const char* kInterfaceCell = "interface bus;\nendinterface\n";
constexpr const char* kInterfaceTop = "module top;\n  bus b();\nendmodule\n";

// The program, the next kind of design element a library holds as a cell.
constexpr const char* kProgramCell = "program pgm;\nendprogram\n";
constexpr const char* kProgramTop = "module top;\n  pgm p();\nendmodule\n";

// The checker, the remaining kind an instantiation reaches by name.
constexpr const char* kCheckerCell = "checker chk;\nendchecker\n";
constexpr const char* kCheckerTop = "module top;\n  chk c1();\nendmodule\n";

// The primitive, which a library holds as a cell as much as it holds a module.
// An instance of one leaves no bound module behind, so what a test reads off
// the design is whether the name reached the primitive at all: reaching it
// leaves the topping cell with no child, while failing to reach it leaves the
// instantiation an unresolved module instance.
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

// A cell is a design element of any kind, so the clause binds an interface as
// it binds a module: gateLib holds the only bus and the default clause leaves
// gateLib out of the search, yet the clause names that library and the instance
// binds the bus held there.
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

// Its companion: the same design under the same default clause with no cell
// clause binds nothing, so above it was the clause that reached the library the
// list leaves out rather than a list carrying gateLib all along.
TEST(ConfigCellClauseExample, WithoutTheClauseTheInterfaceIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "bus", .text = kInterfaceCell, .top = kInterfaceTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "b"), nullptr);
}

// And for a program.
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

// Its companion.
TEST(ConfigCellClauseExample, WithoutTheClauseTheProgramIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "pgm", .text = kProgramCell, .top = kProgramTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "p"), nullptr);
}

// And for a checker.
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

// Its companion.
TEST(ConfigCellClauseExample, WithoutTheClauseTheCheckerIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "chk", .text = kCheckerCell, .top = kCheckerTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "c1"), nullptr);
}

// And for a primitive, which the clause binds on the same terms. gateLib holds
// the only w and the default clause leaves gateLib out, yet the clause names it
// and the name reaches the primitive: the instantiation is an instance of one,
// which leaves the topping cell no module child at all.
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

// Its companion: with no cell clause the same source reaches no primitive and
// no cell of any other kind either, since the only description of w sits in the
// library the list leaves out. The instantiation stays a module instance with
// nothing bound to it, and is reported.
TEST(ConfigCellClauseExample, WithoutTheClauseThePrimitiveIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  SoloCell cell{.base = "w", .text = kPrimitiveCell, .top = kPrimitiveTop};
  auto* top = OnlyTop(ElaborateSoloCell(tmp, design, cell, kNoCellClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  // kPrimitiveTop instantiates w on its fourth line.
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), "unknown module 'w'", 4,
                            "23.3.2"));
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

// The module answering to the primitive's name, for the pair below. It takes
// the same two terminals in the same order, so one instantiation reads as an
// instance of either and the design says which one the name arrived at rather
// than which one the source was written for.
constexpr const char* kRivalModule =
    "module w(output y, input a);\n"
    "  assign y = ~a;\n"
    "endmodule\n";

// Writes a map declaring rtlLib -- holding the topping file and the primitive
// named w -- ahead of gateLib, which holds the module of that name, and
// elaborates a configuration whose default clause lists both libraries and
// whose body `cell_clause` completes. Both libraries are searched and rtlLib is
// searched first, so absent any cell clause the name arrives at the primitive;
// what a clause does to that is the subject of the pair below. Returns the
// design, or nullptr when the map does not load or a file does not parse.
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

// The rejecting side of the binding, read for the primitive. A clause binds the
// name it selects to the one cell it names, so a name it has bound to a cell of
// some other kind has been settled and arrives at no primitive -- not even at
// one held by a library the default clause does list and does search first.
// Here the clause names the gateLib module, so the instantiation stays a module
// instance and binds that module, where the rtlLib primitive of the same name
// would otherwise have taken it.
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

// Its companion, and what makes the claim above about the clause rather than
// about a name that could never have reached a primitive: the same three files
// under the same default clause with no cell clause send the name to the rtlLib
// primitive, which leaves the topping cell no module child at all.
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
