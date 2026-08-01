// Tests for IEEE 1800-2023 §33.6.2 "Using default clause".
//
// The subclause reads the default clause out over the design of §33.6 and
// states four things about it. A default clause names the libraries to search
// and so replaces the search order the library map established, which is what
// makes a library the clause lists ahead of another one searched ahead of it
// whatever the map said. A library the list leaves out is not searched at all,
// so a description held only there is not used. Listing the gate-level library
// ahead of the RTL one therefore takes the gate description of every cell that
// has one. And a listed library holding no description of the cell is passed
// over, so the cell comes from the next listed library that holds one -- which
// is why the design still tops out in the RTL library when the gate-level
// library holds no top.
//
// The rule is applied at the elaborator stage. The list a default clause names
// reaches the elaborator through ApplyConfigDefaultLiblist
// (src/elaborator/elaborator.cpp), which installs it over the order the library
// map yielded, and decides each binding in Elaborator::FindModule,
// PickCandidateByGlobalOrder and PickByLibraryOrder
// (src/elaborator/elaborator_resolve.cpp); a primitive is settled against the
// same list in Elaborator::FindUdpByName
// (src/elaborator/elaborator_items_udp.cpp).
//
// What the rule consumes comes from this pass's dependency. §33.6.1 settles
// what a design binds when no configuration is in force, and it is exactly that
// answer these tests have to see overturned: the library map declares rtlLib
// first, so §33.6.1 binds rtlLib.m and aLib.adder, and a configuration listing
// aLib first or gateLib first has to move those bindings. Every test therefore
// writes the §33.6 library map and source files to disk, loads the map, parses
// each file and tags it through the map, installs the map's own declaration
// order on the elaborator, and only then elaborates a configuration. No test
// states a library or a search order of its own.
//
// A cell is a design element of any kind a library holds, so the exclusion is
// checked over a module, an interface, a program, a checker and a primitive.
// Each of those checks is paired with the same design under a list that does
// name the library, because an instance that binds nothing proves nothing on
// its own: the pair is what shows the list is what turned the binding off.

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"

using namespace delta;

namespace {

// The library map of §33.6: rtlLib is declared first, aLib second, gateLib
// last. Both the aLib and the gateLib specification cover adder.vg, and the
// gateLib specification names that file outright while the aLib one only
// matches it through a wildcard, which is what leaves the gate-level
// descriptions in gateLib and the RTL ones in aLib.
constexpr const char* kExampleMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

// top.v: the cell topping the design instantiates the adder twice, so a claim
// made about every instance of a cell has more than one instance to hold for.
// The file also describes a cell named m, which is the only description of m
// that reaches rtlLib.
constexpr const char* kTopFile =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// The same topping cell with a further instance beside the adder, of a cell
// only top.v describes. rtlLib is the sole library holding a ctrl, so an
// instance of it is what shows a listed library that holds no description of
// the cell being passed over rather than ending the search.
constexpr const char* kTopWithCtrlFile =
    "module top;\n"
    "  adder a1();\n"
    "  ctrl c1();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n"
    "module ctrl;\n"
    "endmodule\n";

// adder.v and adder.vg: the RTL and the gate-level description of the same two
// cells. One text stands for both files, so the descriptions differ in nothing
// a test could have arranged except the library their file names earned them,
// and the adder each file describes instantiates m twice.
constexpr const char* kAdderFile =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// The configuration of §33.6.2 that always takes the m written in adder.v: its
// default clause lists aLib ahead of rtlLib, which is the reverse of the order
// the map declares those two libraries in.
constexpr const char* kCfgRtlFirst =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

// The configuration that adds gateLib at the head of the same list, so the gate
// representation of a cell is taken wherever one exists.
constexpr const char* kCfgGateFirst =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib aLib rtlLib;\n"
    "endconfig\n";

// A configuration whose list names only the library holding the topping cell,
// leaving out both libraries that hold a description of the adder.
constexpr const char* kCfgTopLibraryOnly =
    "config cfg3;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib;\n"
    "endconfig\n";

// A configuration whose list opens with a name no library in the map answers
// to, ahead of the gate-level library. Nothing is held under the leading name,
// so what the design binds says whether the list simply carried on past it.
constexpr const char* kCfgUnmappedFirst =
    "config cfg4;\n"
    "  design rtlLib.top;\n"
    "  default liblist unmappedLib gateLib;\n"
    "endconfig\n";

// A configuration whose default clause leaves the gate-level library out and
// whose cell clause sends the search for one name to a third library. Both
// clauses are in force at once, so what the instance binds says which of them
// governs where the other one found nothing.
constexpr const char* kCfgCellClauseElsewhere =
    "config cfg5;\n"
    "  design rtlLib.top;\n"
    "  default liblist rtlLib aLib;\n"
    "  cell bus liblist aLib;\n"
    "endconfig\n";

// Writes the §33.6 library map and the three source descriptions, taking the
// topping file's text from `top_text`, and parses them with the gate-level file
// first and the topping file last. An implementation binding the description it
// parsed first would answer gateLib throughout, so the parse order cannot be
// what produces any expectation below. Returns false when the map does not load
// or a file does not parse.
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

// Whether any cell bound anywhere under `mod`, `mod` itself included, came from
// `library`. A description a list excludes is not used anywhere in the design
// rather than merely at the instance a test picked out, so the check walks the
// whole elaborated hierarchy.
bool AnyBoundCellFromLibrary(const RtlirModule* mod, std::string_view library) {
  if (mod->library == library) return true;
  for (const auto& child : mod->children) {
    if (child.resolved == nullptr) continue;
    if (AnyBoundCellFromLibrary(child.resolved, library)) return true;
  }
  return false;
}

// The configuration of §33.6.2 that takes the RTL descriptions binds every
// instance of adder to the aLib one. gateLib holds an adder of its own and is
// left out of the list, so it supplies nothing; both instances answer alike,
// which is what a claim about a cell rather than an instance means.
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

// What the configuration is written for: the m definition of adder.v is always
// the one taken. Three libraries hold an m and two of them are on the list, so
// the list order is what chooses between them -- and it chooses against the
// declaration order in the map, which puts rtlLib first and would have bound
// rtlLib.m at every one of these four instances. Every instance of m the design
// reaches answers alike.
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

// The list leaves gateLib out, so no gate-level description is used anywhere in
// the design. The unit holds a gateLib description of both cells the design
// instantiates, and the map declares gateLib among the libraries to search, so
// nothing but the list keeps those descriptions out.
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

// Adding gateLib at the head of the list takes the gate representation of the
// adder ahead of the RTL one. Both libraries are on the list and both hold an
// adder, so the position gateLib was given is the whole of what moved the
// binding -- and it moved it away from the aLib description that both the map's
// declaration order and the previous list bound.
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

// The same list takes the gate representation of m, the cell instantiated
// inside the adder the list just moved to gateLib. Three libraries hold an m
// and all three are on the list, so the head of the list is what decides, and
// the descriptions taken for both cells come from adder.vg.
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

// A listed library holding no description of the cell is passed over rather
// than ending the search, so the cell comes from the next listed library that
// holds one -- which is why the design still tops out in rtlLib with gateLib at
// the head of the list. The design reads both halves out of one elaboration:
// the adder takes the gate description because gateLib holds one, and ctrl
// takes the rtlLib description because neither gateLib nor aLib does.
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

// The nearest input the exclusion has to turn away: an instance of a cell whose
// every description lives in a library the list leaves out. Only aLib and
// gateLib hold an adder and the list names neither, so both adder instances are
// reported and left unbound rather than filled in from a library the list
// passed over.
TEST(ConfigDefaultClauseExample, CellHeldOnlyByUnlistedLibrariesIsUnbound) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kTopFile));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "aLib"));
  ASSERT_TRUE(DesignHoldsCell(d.unit, "adder", "gateLib"));

  auto* top = OnlyTop(ElaborateConfigText(tmp, d, kCfgTopLibraryOnly));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(d.diag.HasErrors());
  ASSERT_EQ(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].resolved, nullptr);
}

// One cell described in one file of its own, for the tests that vary the kind
// of design element a library holds. `base` names the file -- base.vg, which
// the §33.6 map sends to gateLib -- `cell` is the description written into it,
// and `top` describes the cell instantiating it once.
struct OneLibraryCell {
  std::string base;
  std::string cell;
  std::string top;
};

// The configuration the tests below elaborate: it names the topping cell in
// rtlLib, so the design root is settled by the design statement rather than by
// the list, and hands its default clause the library list under test.
std::string DefaultClauseConfig(std::string_view liblist) {
  std::string text = "config cfg;\n  design rtlLib.top;\n  default liblist ";
  text += liblist;
  text += ";\nendconfig\n";
  return text;
}

// Writes a map holding the topping file in rtlLib and `c.base`.vg in gateLib,
// parses both files, and elaborates a configuration whose default clause names
// `liblist`. gateLib holds the only description of the instantiated cell, so
// whether the instance binds anything is decided by whether that library is on
// the list. Returns the design, or nullptr when the map does not load or a file
// does not parse.
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

// The two library lists the tests below run under. One names only the library
// holding the topping cell, leaving out the library that holds the only
// description of the instantiated cell; the other names both. An instance that
// binds nothing proves nothing on its own, so each exclusion is read against
// the same design under the list that does name the library.
constexpr const char* kGateOmitted = "rtlLib";
constexpr const char* kGateListed = "rtlLib gateLib";

// The interface described in the file the map sends to gateLib, and the cell
// instantiating it.
constexpr const char* kBusCell = "interface bus;\nendinterface\n";
constexpr const char* kBusTop = "module top;\n  bus b();\nendmodule\n";

// The program, the next kind of design element a library holds as a cell.
constexpr const char* kPgmCell = "program pgm;\nendprogram\n";
constexpr const char* kPgmTop = "module top;\n  pgm p();\nendmodule\n";

// The checker, the remaining kind an instantiation reaches.
constexpr const char* kChkCell = "checker chk;\nendchecker\n";
constexpr const char* kChkTop = "module top;\n  chk c1();\nendmodule\n";

// The primitive, which a library holds as a cell as much as a module. An
// instance of one leaves no bound module behind, so what a test reads off the
// design is whether the name reached the primitive at all: reaching it leaves
// the topping cell with no child, while failing to reach it leaves the
// instantiation an unresolved module instance.
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

// A cell is a design element of any kind, so the exclusion covers an interface
// as it covers a module: gateLib holds the only bus and the list leaves gateLib
// out, so the instance binds nothing.
TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAnInterface) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "bus", .cell = kBusCell, .top = kBusTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "b"), nullptr);
}

// Its companion, and with it the pass-over for a cell kind other than a
// module: naming gateLib on the list binds the same instance to the same
// description, so the list is what turned the binding off above rather than an
// interface instance that could not have bound in either case. rtlLib heads
// this list and holds the topping cell but no bus, so the search reaching
// gateLib at all is a listed library holding no description of the cell being
// passed over rather than ending the search.
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

// And for a program.
TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAProgram) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "pgm", .cell = kPgmCell, .top = kPgmTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "p"), nullptr);
}

// Its companion.
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

// And for a checker.
TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAChecker) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "chk", .cell = kChkCell, .top = kChkTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "c1"), nullptr);
}

// Its companion.
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

// And for a primitive, which the list settles on the same terms. gateLib holds
// the only w and the list leaves it out, so the name reaches no primitive and
// no cell of any other kind either: the instantiation stays a module instance
// with nothing bound to it, and is reported.
TEST(ConfigDefaultClauseExample, UnlistedLibraryDoesNotSupplyAPrimitive) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "w", .cell = kPrimCell, .top = kPrimTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateOmitted));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(d.unit, "w", "gateLib"));
  EXPECT_TRUE(d.diag.HasErrors());
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

// Its companion, and the same pass-over for a primitive: with gateLib on the
// list the same source reaches the primitive, so the instantiation is an
// instance of it and leaves the topping cell no module child at all. rtlLib is
// listed ahead of gateLib and holds no cell named w, so it is passed over on
// the way there.
TEST(ConfigDefaultClauseExample, ListedLibrarySuppliesAPrimitive) {
  ScratchDir tmp;
  LibraryDesign d;
  OneLibraryCell cell{.base = "w", .cell = kPrimCell, .top = kPrimTop};
  auto* top = OnlyTop(ElaborateOneLibraryCell(tmp, d, cell, kGateListed));
  ASSERT_NE(top, nullptr);
  EXPECT_FALSE(d.diag.HasErrors());
  EXPECT_TRUE(top->children.empty());
}

// The list is the search order, so a name on it that no library answers to
// takes its position and supplies nothing rather than ending the search there.
// The list opens with such a name and then names gateLib, and the design binds
// the gate-level descriptions throughout -- which is also against the answer
// the map's declaration order gives, since that puts aLib and rtlLib ahead of
// gateLib for the adder and for the m nested inside it.
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

// A cell described in two files, for the tests over a name two libraries
// answer to. `base` names the pair -- base.vg, which the map sends to gateLib,
// and base.v, which it sends to rtlLib beside the topping file -- `gate` and
// `rtl` are the descriptions written into them, and `top` describes the cell
// instantiating the name once.
struct TwoLibraryCell {
  std::string base;
  std::string gate;
  std::string rtl;
  std::string top;
};

// The pair for a name both libraries answer to with the same description:
// `cell` is written to both files, so the two differ in nothing a test could
// have arranged except the library their file name earned them.
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

// The pair for a name the two libraries answer to differently: `gate` goes to
// the gateLib file and `rtl` to the rtlLib one. That is how a test puts one
// kind of design element in one library and another kind -- or no cell of the
// name at all -- in the other.
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

// Writes a map declaring gateLib first, holding `c.base`.vg, and rtlLib second,
// holding the topping file and `c.base`.v; parses the gate-level file before
// the RTL one; and elaborates a configuration whose default clause names
// `liblist`. gateLib is declared first and its file is parsed first, so both
// the declaration order and the parse order answer gateLib wherever the two
// libraries hold the name -- an expectation of rtlLib below can only come from
// the list. Returns the design, or nullptr when the map does not load or a file
// does not parse.
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

// The module answering to the primitive's name, for the tests that put a
// primitive in one library and a design element of another kind in the other.
// Both take the same two terminals, so one instantiation reads as an instance
// of either.
constexpr const char* kPrimAsModule =
    "module w(output y, input a);\n"
    "  assign y = ~a;\n"
    "endmodule\n";

// The exclusion where both libraries hold a description of the name, for an
// interface. The map declares gateLib first, so the declaration order alone
// binds the gateLib bus; the list names rtlLib and leaves gateLib out, so the
// rtlLib description is what the instance takes instead.
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

// The same for a program held by both libraries.
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

// And for a checker held by both libraries.
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

// And for a primitive, which a name reaches only where no design element of
// another kind sits in a library searched ahead of it. The gateLib file holds
// the primitive and the rtlLib file a module of the name; the list names rtlLib
// alone, so the primitive's library is not searched and the name arrives at the
// module, leaving a bound child where reaching the primitive would leave none.
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

// Its companion: with gateLib at the head of the list its primitive is searched
// first, so the name reaches the primitive and the module in the library listed
// after it is passed over -- the topping cell is left with no bound child at
// all. The same two files serve both tests, so the list order is the whole of
// what differs.
TEST(ConfigDefaultClauseExample, ListedPrimitiveTakesTheNameFromTheModule) {
  ScratchDir tmp;
  LibraryDesign d;
  auto cell = DifferentInEachLibrary("w", kPrimCell, kPrimAsModule, kPrimTop);
  auto* top = OnlyTop(ElaborateTwoLibraryCell(tmp, d, cell, "gateLib rtlLib"));
  ASSERT_NE(top, nullptr);
  EXPECT_FALSE(d.diag.HasErrors());
  EXPECT_TRUE(top->children.empty());
}

// A description of some other cell, for a library meant to hold no cell of the
// name under test.
constexpr const char* kSpareCell = "module spare;\nendmodule\n";

// The exclusion belongs to the default clause, so it holds however the search
// for a name proceeded. gateLib holds the only bus and the default clause
// leaves gateLib out; a cell clause then sends the search for that name to
// aLib, which the default clause does list but which holds no bus. The
// narrower clause coming up empty does not put the excluded library back into
// play: the instance is left unbound rather than filled in from gateLib.
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
}

}  // namespace
