// Tests for IEEE 1800-2023 §33.6.4 "Using instance clause".
//
// The subclause reads an instance selection clause paired with a library list
// out over the design of §33.6 and states two things about it. The list the
// clause names governs the instance the clause names, so that instance is bound
// out of a library the configuration's own default clause need never have
// listed. And the list is inherited: every descendant of the named instance is
// bound out of it too, however far below it they sit. What the clause does not
// name it does not reach, so a sibling, an ancestor and the design's own top
// cell are left to the default clause -- which is how one configuration gives
// one adder the gate-level representation and the other the RTL one.
//
// The rule is applied at the elaborator stage. An instance clause's library
// list reaches the elaborator through CollectInstanceLiblistOverrides
// (src/elaborator/elaborator.cpp) and decides which list governs a binding in
// InstanceLiblistForPath (src/elaborator/elaborator_helpers.h), which
// Elaborator::FindModule consults through SelectOverrideLiblist ahead of the
// order the default clause installed (src/elaborator/elaborator_resolve.cpp).
// A primitive is settled against the same list in Elaborator::FindUdpByName,
// under the path Elaborator::ReclassifyForwardUdpInstances puts the searched
// instantiation at (src/elaborator/elaborator_items_udp.cpp).
//
// What the rule consumes comes from this pass's dependencies: §33.6.1's library
// map and declaration order, and §33.6.2's default clause. It is §33.6.2's
// answer this clause overturns for one subhierarchy and leaves standing
// everywhere else -- under the §33.6 map the list `gateLib rtlLib`
// takes the gate-level description of every cell that has one, so a clause
// naming aLib at top.a2 has to move that instance and its descendants, and only
// those. Every test therefore writes the §33.6 library map and source files to
// disk, loads the map, parses each file and tags it through the map, installs
// the map's own declaration order on the elaborator, and only then elaborates a
// configuration. No test states a library or a search order of its own, and
// every claim about a moved binding is paired with the same design elaborated
// without the clause, since a binding that would have landed there anyway shows
// nothing.
//
// A cell is a design element of any kind a library holds, so both halves of the
// rule are read over a module, an interface, a program, a checker and a
// primitive: once for the kind a descendant instantiates, once for the kind the
// named instance is itself an instance of. The module case is the §33.6 design;
// the others put the only description of the cell in a library the default
// clause leaves out, so the clause's list alone decides.

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
// last. Both the aLib and the gateLib specification cover adder.vg, and only
// gateLib's names that file outright, which is what leaves the gate-level
// descriptions in gateLib and the RTL ones in aLib.
constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

// top.v: the cell topping the design instantiates the adder twice, so a clause
// naming one of them has a sibling to leave alone. Its cell named m is the only
// m that reaches rtlLib.
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
// adder each describes instantiates m twice -- the descendants an instance
// clause naming an adder has to reach.
constexpr const char* kAdderSource =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// The configuration of §33.6.4. Its default clause lists the gate-level library
// first, so every cell with a gate-level description takes it; its instance
// clause then names aLib -- absent from that list -- at the second adder.
constexpr const char* kConfigWithInstanceClause =
    "config cfg4;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a2 liblist aLib;\n"
    "endconfig\n";

// The configuration of §33.6.2 that this one modifies: the same default clause
// with the instance clause struck out -- the answer to overturn at top.a2 and
// to leave standing at top.a1.
constexpr const char* kConfigWithoutInstanceClause =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "endconfig\n";

// The nearest input the selection has to turn away: a path running through the
// opening characters of two real instance paths without naming either. The
// design holds top.a1 and top.a2 and holds no top.a.
constexpr const char* kConfigPathNamingNoInstance =
    "config cfg8;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a liblist aLib;\n"
    "endconfig\n";

// The same clause written at a deeper instance: what a clause reaches is the
// instance its path names, whichever level of the hierarchy that path stops at.
constexpr const char* kConfigDeeperInstancePath =
    "config cfg9;\n"
    "  design rtlLib.top;\n"
    "  default liblist gateLib rtlLib;\n"
    "  instance top.a1.f1 liblist aLib;\n"
    "endconfig\n";

// Writes the §33.6 library map and the three source descriptions and parses
// them with the RTL file first and the topping file last. An implementation
// binding whichever description it parsed first would answer aLib everywhere,
// which each pairing below rules out: the same files under a configuration
// carrying no instance clause answer gateLib at every binding the clause is
// claimed to have moved. Returns false when a file does not parse.
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

// The libraries the two adders bound out of, in the order the topping cell
// instantiates them.
std::vector<std::string> LibrariesBindingTheAdders(RtlirModule* top) {
  return LibrariesBound(top, {"a1", "a2"});
}

// The libraries the four cells named m bound out of, ordered a1.f1, a1.f2,
// a2.f1, a2.f2: the descendants of the instance a clause names read beside the
// descendants of the instance it does not.
std::vector<std::string> LibrariesBindingM(RtlirModule* top) {
  return LibrariesBoundBeneath(top, {"a1", "a2"}, {"f1", "f2"});
}

// The clause names a library list for the instance it selects, and that list is
// what the instance is bound out of: top.a2 comes from aLib, a library the
// configuration's default clause does not list at all, while the design still
// holds the gate-level adder that clause would otherwise have taken.
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

// The answer the clause overturns, read off the same design under the same
// default clause with the instance clause struck out: the list names the
// gate-level library first and both adders come from it. The pair is what shows
// the clause moved the second one, since a binding the default clause would
// have produced anyway proves nothing.
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

// The list is inherited, so it decides the bindings below the named instance as
// well as that instance itself: both cells named m inside top.a2 come from
// aLib. Both libraries the default clause lists hold an m and neither supplies
// one here, so the inherited list is what settled them.
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

// Its companion: with the instance clause struck out, all four cells named m
// come from the gate-level library the default clause lists first. The two
// under top.a2 are the ones the inherited list moved, and this is where they
// would have landed without it.
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

// What the clause selects is one instance, so the sibling and everything under
// it are left to the default clause: read in the very elaboration that moved
// top.a2 onto aLib, top.a1 and both cells named m beneath it still come from
// the gate-level library, and the design still tops out where the design
// statement put it.
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

// A path is inherited down levels of hierarchy, not across the spelling of a
// name: the clause here names top.a, which runs through the opening characters
// of top.a1 and top.a2 and names neither instance. It therefore reaches
// nothing, and every binding in the design is the one the default clause gives
// -- the gate-level adder twice over and the gate-level m four times.
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

// The path a clause carries may stop at any level, and what it names is the
// instance it stops at with what hangs below it. This clause names top.a1.f1, a
// cell with no descendants: that one cell comes from aLib, and its sibling, its
// parent and the whole other adder stay where the default clause puts them.
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

// One cell described in a file of its own, for the tests that vary the kind of
// design element under test. `base` names the file -- base.vg, which the map
// below sends to gateLib -- `text` is the description written into it, and
// `top` is the topping file, describing the cells that instantiate it.
struct NestedCell {
  std::string base;
  std::string text;
  std::string top;
};

// The instance clause the tests below elaborate: it names the one instance the
// topping cell holds and a list carrying the library that the only description
// of the cell instantiated one level further down sits in.
constexpr const char* kInstanceClauseReachingGateLib =
    "  instance top.m1 liblist rtlLib gateLib;\n";

// The configuration body carrying no instance clause, for the companion of each
// pair below.
constexpr const char* kNoInstanceClause = "";

// Writes a map holding the topping file in rtlLib and `cell.base`.vg in
// gateLib, parses both files, and elaborates a configuration naming the topping
// cell, whose default clause names rtlLib alone -- leaving out the library
// holding the only description of the cell under test -- and whose body
// `inst_clause` completes. Returns nullptr when a file fails.
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

// The cell the instance clause names, reached through the design's top cell, or
// nullptr where the design bound nothing there.
RtlirModule* NamedInstanceOf(RtlirDesign* design) {
  auto* top = OnlyTop(design);
  if (top == nullptr) return nullptr;
  return ChildBoundTo(top, "m1");
}

// The interface described in the file the map sends to gateLib, and the two
// cells the topping file describes: the one the clause names and the one that
// instantiates the interface.
constexpr const char* kInterfaceCell = "interface bus;\nendinterface\n";
constexpr const char* kInterfaceTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  bus b();\n"
    "endmodule\n";

// The program, the next kind of design element a library holds as a cell.
constexpr const char* kProgramCell = "program pgm;\nendprogram\n";
constexpr const char* kProgramTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  pgm p();\n"
    "endmodule\n";

// The checker, the remaining kind an instantiation reaches by name.
constexpr const char* kCheckerCell = "checker chk;\nendchecker\n";
constexpr const char* kCheckerTop =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  chk c1();\n"
    "endmodule\n";

// The primitive, which a library holds as a cell as much as it holds a module.
// An instance of one leaves no bound module behind, so what a test reads is
// whether the name reached the primitive at all: reaching it leaves the
// instantiating cell no child, failing to reach it leaves an unresolved
// module instance.
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

// A module described three levels below the topping cell, for the pair reading
// how far down the inheritance runs.
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

// A cell is a design element of any kind, so a descendant inherits the list for
// an interface as it does for a module: gateLib holds the only bus, the default
// clause leaves gateLib out, and the clause names it one level above.
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

// Its companion: the same design under the same default clause with no instance
// clause binds nothing there, so above it was the inherited list that reached
// the excluded library rather than a default clause carrying it all along.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheInterfaceIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "bus", .text = kInterfaceCell, .top = kInterfaceTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(mid, "b"), nullptr);
}

// And for a program.
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

// Its companion.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheProgramIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "pgm", .text = kProgramCell, .top = kProgramTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(mid, "p"), nullptr);
}

// And for a checker.
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

// Its companion.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheCheckerIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "chk", .text = kCheckerCell, .top = kCheckerTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(mid, "c1"), nullptr);
}

// And for a primitive, which a descendant reaches through the inherited list
// on the same terms. gateLib holds the only w and the default clause leaves
// gateLib out, yet the clause hands the instance below it a list naming that
// library and the name reaches the primitive: the instantiation is an instance
// of one, which leaves the instantiating cell no module child at all.
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

// Its companion: with no instance clause the same source reaches no primitive
// and no cell of any other kind, since the only description of w sits in the
// excluded library. The instantiation stays an unbound module instance.
TEST(ConfigInstanceClauseExample, WithoutTheClauseThePrimitiveIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "w", .text = kPrimitiveCell, .top = kPrimitiveTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_TRUE(design.diag.HasErrors());
  ASSERT_EQ(mid->children.size(), 1u);
  EXPECT_EQ(mid->children[0].resolved, nullptr);
}

// Inheritance is not a rule about children: the list reaches every descendant,
// so a cell two levels below the named instance is bound out of it too. gateLib
// holds the only leaf, the default clause leaves gateLib out, and the clause
// names the grandparent of the instance that binds it.
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

// Its companion, two levels down.
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
}

// The topping file of the tests below: the cell the clause names sits between
// the design's top cell and the cell instantiating the leaf.
constexpr const char* kNarrowedTopSource =
    "module top;\n"
    "  mid m1();\n"
    "endmodule\n"
    "module mid;\n"
    "  leaf u();\n"
    "endmodule\n";

// The instance clause of the pair below: it hands the named instance a list
// that holds the cell that instance is bound out of and does not hold the
// library the cell beneath it is described in.
constexpr const char* kInstanceClauseWithoutTheLeaf =
    "  instance top.m1 liblist rtlLib;\n";

// Writes a map holding the topping file in rtlLib and the leaf's file in
// gateLib and elaborates a configuration whose default clause names both
// libraries and whose body `inst_clause` completes. That clause holds the
// leaf's library, so what an instance clause naming a narrower list does is the
// whole of what the tests below turn on. Returns nullptr when a file fails.
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

// The rejecting side of the inheritance. What a descendant inherits is the
// clause's list, not an addition to the default clause's, so a cell described
// only outside the inherited list is not bound -- even though the default
// clause lists the library holding it. The clause names rtlLib at top.m1, and
// the leaf held only by gateLib is left unbound below it.
TEST(ConfigInstanceClauseExample, InheritedListWithoutTheCellLeavesItUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  auto* elaborated =
      ElaborateNarrowedSubtree(tmp, design, kInstanceClauseWithoutTheLeaf);
  auto* mid = NamedInstanceOf(elaborated);
  ASSERT_NE(mid, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "leaf", "gateLib"));
  EXPECT_TRUE(design.diag.HasErrors());
  EXPECT_EQ(ChildBoundTo(mid, "u"), nullptr);
}

// Its companion, and what makes the claim above about the inherited list rather
// than about a cell nothing could have reached: the same two files under the
// same default clause with no instance clause bind the leaf out of gateLib.
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

// The nearest input the clause's own binding has to turn away: a list holding
// no description of the cell the named instance is an instance of. The default
// clause lists both libraries and rtlLib holds the only mid; the clause names
// gateLib alone.
constexpr const char* kClauseListWithoutTheCell =
    "  instance top.m1 liblist gateLib;\n";

// A clause's list is the list its instance is bound out of, so a cell that list
// does not hold is not reached: the instance is reported and left unbound
// rather than filled in from the library the default clause does list.
TEST(ConfigInstanceClauseExample, ClauseListLackingTheCellLeavesItUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  auto* elaborated =
      ElaborateNarrowedSubtree(tmp, design, kClauseListWithoutTheCell);
  auto* top = OnlyTop(elaborated);
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "mid", "rtlLib"));
  EXPECT_TRUE(design.diag.HasErrors());
  EXPECT_EQ(ChildBoundTo(top, "m1"), nullptr);
}

// The topping files below instantiate the cell under test themselves, so what
// these pairs vary is the kind of cell the named instance is an instance of,
// where the pairs above varied the kind of what hangs below it. The instance is
// called x throughout, so one clause serves every kind.
constexpr const char* kSoloIfaceTop = "module top;\n  bus x();\nendmodule\n";
constexpr const char* kSoloProgTop = "module top;\n  pgm x();\nendmodule\n";
constexpr const char* kSoloChkTop = "module top;\n  chk x();\nendmodule\n";
constexpr const char* kSoloPrimTop =
    "module top;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w x(y, a);\n"
    "endmodule\n";

// The clause naming that instance, with a list carrying the library that holds
// the only description of the cell it is an instance of.
constexpr const char* kSoloClause =
    "  instance top.x liblist rtlLib gateLib;\n";

// What a clause names is an instance, and an instance is of a cell of any kind
// a library holds. Naming an interface instance binds it out of the clause's
// list: gateLib holds the only bus and the default clause leaves gateLib out.
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

// Its companion: with no clause the same source binds nothing there, so it was
// the clause's list and not the default clause's that reached the library.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedInterfaceIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "bus", .text = kInterfaceCell, .top = kSoloIfaceTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "bus", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "x"), nullptr);
}

// And for an instance of a program.
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

// Its companion.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedProgramIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "pgm", .text = kProgramCell, .top = kSoloProgTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "pgm", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "x"), nullptr);
}

// And for an instance of a checker.
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

// Its companion.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedCheckerIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "chk", .text = kCheckerCell, .top = kSoloChkTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "chk", "gateLib"));
  EXPECT_EQ(ChildBoundTo(top, "x"), nullptr);
}

// And for an instance of a primitive. An instantiation is settled as an
// instance of one while the cell holding it is elaborated, a level above the
// path the clause carries, so this is the case that says a clause naming the
// instance itself is consulted: reaching the primitive leaves the topping cell
// no module child at all.
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

// Its companion: with no clause the name reaches no primitive, since the only
// description of w sits in the excluded library, and the instantiation stays an
// unbound module instance.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheNamedPrimitiveIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "w", .text = kPrimitiveCell, .top = kSoloPrimTop};
  auto* top =
      OnlyTop(ElaborateNestedCell(tmp, design, cell, kNoInstanceClause));
  ASSERT_NE(top, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "w", "gateLib"));
  EXPECT_TRUE(design.diag.HasErrors());
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

// The level of hierarchy the list is inherited through need not be a module
// either: top.m1 is an instance of an interface here, and the cell that
// interface instantiates is held only by the library the default clause omits.
constexpr const char* kInterfaceLevelTop =
    "module top;\n"
    "  bus m1();\n"
    "endmodule\n"
    "interface bus;\n"
    "  leaf u();\n"
    "endinterface\n";

// A descendant reached through an interface inherits the list as one reached
// through a module does: the interface comes from the library the default
// clause names, the cell inside it from the library only the clause reaches.
TEST(ConfigInstanceClauseExample, InheritedListPassesThroughAnInterface) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "leaf", .text = kDeepCell, .top = kInterfaceLevelTop};
  auto* elaborated =
      ElaborateNestedCell(tmp, design, cell, kInstanceClauseReachingGateLib);
  auto* bus = NamedInstanceOf(elaborated);
  ASSERT_NE(bus, nullptr);
  EXPECT_TRUE(bus->is_interface);
  auto* bound = ChildBoundTo(bus, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

// Its companion.
TEST(ConfigInstanceClauseExample, WithoutTheClauseTheCellBelowIsUnbound) {
  ScratchDir tmp;
  LibraryDesign design;
  NestedCell cell{.base = "leaf", .text = kDeepCell, .top = kInterfaceLevelTop};
  auto* elaborated = ElaborateNestedCell(tmp, design, cell, kNoInstanceClause);
  auto* bus = NamedInstanceOf(elaborated);
  ASSERT_NE(bus, nullptr);
  ASSERT_TRUE(DesignHoldsCell(design.unit, "leaf", "gateLib"));
  EXPECT_EQ(ChildBoundTo(bus, "u"), nullptr);
}

}  // namespace
