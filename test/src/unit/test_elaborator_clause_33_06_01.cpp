// Tests for IEEE 1800-2023 §33.6.1 "Default configuration from library map
// file".
//
// The subclause states one rule and reads it out over the design of §33.6:
// with no configuration in force, the libraries are searched in the order the
// library map file declares them, so an instance binds the description held by
// the first declared library that holds a cell of that name. In the §33.6
// design that makes every instance of `adder` bind the aLib description --
// rtlLib is declared first but holds no adder -- and every instance of `m`
// bind the rtlLib description, including the m instances written inside the
// aLib adder.
//
// The rule is applied at the elaborator stage. The search order reaches the
// elaborator through Elaborator::SetLibraryDeclarationOrder
// (src/elaborator/elaborator.cpp) and decides the binding in
// Elaborator::FindModule and PickByLibraryOrder
// (src/elaborator/elaborator_resolve.cpp); the order itself is what
// LibraryMap::ResolveSearchOrder (src/parser/library_map.cpp) yields for an
// invocation that named no order of its own.
//
// What the rule consumes comes from this pass's dependencies: the library
// declarations and the order they are declared in are read from a real lib.map
// (§33.3.1), and the library each cell lives in is the one the map's file path
// specifications earned that cell's source file (§33.3.3). Every test below
// therefore writes the map and the source files to disk, loads the map, parses
// each file and tags it through the map, and elaborates the assembled unit. No
// test states a library or a search order of its own.
//
// A primitive is a cell a library holds as much as a module is. An instance of
// one keeps no record of the description it took, so which of two libraries
// holding a primitive of the name supplied it cannot be read back. What can be
// read back is whether the name reached a primitive at all: a name reaching a
// module instead leaves a bound module instance where reaching the primitive
// leaves none. The tests over that cell kind therefore put a primitive and a
// design element of another kind in different libraries and read which one the
// search arrived at.

#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_scratch_dir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// The library map of §33.6: rtlLib is declared first, aLib second, gateLib
// last. Both the aLib and the gateLib specification cover adder.vg, and the
// gateLib specification names that file outright while the aLib one only
// matches it through a wildcard, which is what leaves the gate-level
// descriptions in gateLib and the RTL ones in aLib. The declaration order and
// the library each file lands in are therefore two separate things, and the
// tests below turn one without turning the other.
constexpr const char* kExampleMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

// top.v: the cell topping the design instantiates the adder twice, so a rule
// said to hold for every instance of a cell has more than one instance to hold
// for. The file also describes a cell named m, which is the only description of
// m that reaches rtlLib.
constexpr const char* kTopFile =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// adder.v and adder.vg: the RTL and the gate-level description of the same two
// cells. One text stands for both files, so the descriptions differ in nothing
// a test could have arranged except the library their file names earned them,
// and the adder each file describes instantiates m twice -- the instances whose
// binding §33.6.1 settles against the library holding their parent.
constexpr const char* kAdderFile =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// The adder on its own, for a further file added to a library that already
// holds a description of m. Two cells of one name in one library would be two
// definitions of the same cell rather than the choice between libraries these
// tests are about.
constexpr const char* kAdderOnlyFile =
    "module adder;\n"
    "  m f1();\n"
    "  m f2();\n"
    "endmodule\n";

// One compilation unit assembled out of several source files, the way a tool
// handed several files assembles one. Each file is parsed on its own and its
// cells are written into the library its path maps to, so every library named
// in an expectation below was established by a map read off disk rather than
// written onto the cells by a test.
struct MappedDesign {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap map;
  CompilationUnit* unit = nullptr;

  bool ParseFile(const fs::path& path, const std::string& src);
};

// Appends every element of `src` to `dst`.
template <typename T>
void AppendAll(std::vector<T>& dst, const std::vector<T>& src) {
  dst.insert(dst.end(), src.begin(), src.end());
}

bool MappedDesign::ParseFile(const fs::path& path, const std::string& src) {
  auto fid = mgr.AddFile(path.string(), src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  if (cu == nullptr || diag.HasErrors()) return false;
  map.TagCompilationUnit(*cu, path.string());
  if (unit == nullptr) {
    unit = cu;
    return true;
  }
  AppendAll(unit->modules, cu->modules);
  AppendAll(unit->interfaces, cu->interfaces);
  AppendAll(unit->programs, cu->programs);
  AppendAll(unit->checkers, cu->checkers);
  AppendAll(unit->udps, cu->udps);
  AppendAll(unit->packages, cu->packages);
  AppendAll(unit->configs, cu->configs);
  return true;
}

// Writes the library map and the three source descriptions of §33.6, then
// parses them with the gate-level file first and the topping file last. An
// implementation binding the description it parsed first, rather than the one
// the declaration order names, would answer gateLib for the adder, so the
// parse order cannot be what produces the expected answer. Returns false when
// the map does not load or a file does not parse.
bool BuildExampleDesign(ScratchDir& tmp, MappedDesign& d,
                        const std::string& map_text) {
  auto map_file = tmp.Write("lib.map", map_text);
  auto gate = tmp.Write("adder.vg", kAdderFile);
  auto rtl = tmp.Write("adder.v", kAdderFile);
  auto top = tmp.Write("top.v", kTopFile);
  if (!d.map.LoadMapFile(map_file)) return false;
  return d.ParseFile(gate, kAdderFile) && d.ParseFile(rtl, kAdderFile) &&
         d.ParseFile(top, kTopFile);
}

// A module and a primitive answering to one name, each written to a file of its
// own so the map decides which library holds which. Both take the same two
// terminals, so one instantiation reads as an instance of either.
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

// One cell described in two files, for the tests that vary the kind of design
// element the cell is made from. `base` names the pair of files -- base.v and
// base.vg -- `cell` is the description written into each of them, and `top`
// describes the cell instantiating it once.
struct TwoFileCell {
  std::string base;
  std::string cell;
  std::string top;
};

// Writes a map sending base.v to aLib and base.vg to gateLib, with rtlLib
// declared ahead of both and holding the topping file, then parses the
// gate-level file before the RTL one. aLib is declared before gateLib and
// rtlLib holds no cell of the name, so a search following the declaration order
// answers aLib whatever kind of design element the cell is. Returns false when
// the map does not load or a file does not parse.
bool BuildTwoFileCellDesign(ScratchDir& tmp, MappedDesign& d,
                            const TwoFileCell& c) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library aLib " + c.base + ".v;\n";
  map_text += "library gateLib " + c.base + ".vg;\n";
  auto map_file = tmp.Write("lib.map", map_text);
  auto gate = tmp.Write(c.base + ".vg", c.cell);
  auto rtl = tmp.Write(c.base + ".v", c.cell);
  auto top = tmp.Write("top.v", c.top);
  if (!d.map.LoadMapFile(map_file)) return false;
  return d.ParseFile(gate, c.cell) && d.ParseFile(rtl, c.cell) &&
         d.ParseFile(top, c.top);
}

// Elaborates `top_cell` with no configuration in force, under exactly the
// search order the loaded map yields for an invocation that named no library
// order of its own.
RtlirDesign* ElaborateUnderMapOrder(MappedDesign& d,
                                    std::string_view top_cell) {
  Elaborator elab(d.arena, d.diag, d.unit);
  elab.SetLibraryDeclarationOrder(d.map.ResolveSearchOrder({}));
  return elab.Elaborate(top_cell);
}

// The one top module an elaborated design holds, or nullptr when it holds none
// or holds several.
RtlirModule* SoleTop(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return nullptr;
  return design->top_modules[0];
}

// The module bound to the instance named `inst_name` under `parent`, or nullptr
// when `parent` holds no instance of that name.
RtlirModule* BoundChild(RtlirModule* parent, std::string_view inst_name) {
  for (const auto& child : parent->children) {
    if (child.inst_name == inst_name) return child.resolved;
  }
  return nullptr;
}

// Whether any declaration in `decls` is named `name` and lives in `library`.
// Every kind of design element carries both, so one walk serves them all.
template <typename Decls>
bool DeclsHoldCell(const Decls& decls, std::string_view name,
                   std::string_view library) {
  for (const auto* decl : decls) {
    if (decl->name == name && decl->library == library) return true;
  }
  return false;
}

// Whether the assembled unit holds a cell named `name` in `library`, over every
// kind of design element the search covers. Each test naming a library that
// wins the search also names one that lost it, so a design that never held the
// passed-over description cannot pass for one that held it and was searched
// later.
bool UnitHoldsCell(const CompilationUnit* unit, std::string_view name,
                   std::string_view library) {
  return DeclsHoldCell(unit->modules, name, library) ||
         DeclsHoldCell(unit->interfaces, name, library) ||
         DeclsHoldCell(unit->programs, name, library) ||
         DeclsHoldCell(unit->checkers, name, library) ||
         DeclsHoldCell(unit->udps, name, library);
}

// The first half of the rule as §33.6.1 reads it out: no configuration is
// elaborated, so the libraries are searched in declaration order, and every
// instance of adder binds aLib.adder. rtlLib is declared ahead of aLib and is
// searched first, but holds no cell named adder, so the search passes it by;
// gateLib holds one and is searched after aLib, so it is passed over. Both
// instances answer alike, which is what "all instances" claims.
TEST(DefaultLibraryBinding, EveryAdderInstanceBindsFirstDeclaredLibraryWithIt) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "adder", "gateLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = BoundChild(top, "a1");
  auto* a2 = BoundChild(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a1->name, "adder");
  EXPECT_EQ(a1->library, "aLib");
  EXPECT_EQ(a2->library, "aLib");
}

// The second half: every instance of m binds rtlLib.m, and the instances of m
// that the design reaches are the ones written inside the adder the first half
// left bound out of aLib. aLib holds a cell named m of its own -- adder.v
// describes one -- and it is the library the parent came from, but the search
// starts again from the head of the declaration order for the instance rather
// than following the parent's library, so rtlLib answers.
TEST(DefaultLibraryBinding, NestedMInstancesBindFirstDeclaredLibraryWithM) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "m", "aLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = BoundChild(top, "a1");
  ASSERT_NE(a1, nullptr);
  ASSERT_EQ(a1->library, "aLib");
  auto* f1 = BoundChild(a1, "f1");
  auto* f2 = BoundChild(a1, "f2");
  ASSERT_NE(f1, nullptr);
  ASSERT_NE(f2, nullptr);
  EXPECT_EQ(f1->name, "m");
  EXPECT_EQ(f1->library, "rtlLib");
  EXPECT_EQ(f2->library, "rtlLib");

  // The claim is about every instance of m, and the design reaches four of
  // them: the second adder instance carries two more.
  auto* a2 = BoundChild(top, "a2");
  ASSERT_NE(a2, nullptr);
  auto* g1 = BoundChild(a2, "f1");
  auto* g2 = BoundChild(a2, "f2");
  ASSERT_NE(g1, nullptr);
  ASSERT_NE(g2, nullptr);
  EXPECT_EQ(g1->library, "rtlLib");
  EXPECT_EQ(g2->library, "rtlLib");
}

// What decides the binding is the order the map declares the libraries in, so
// moving the gateLib declaration ahead of the aLib one moves the binding with
// it. The two file path specifications are unchanged and each file still lands
// in the library it landed in before -- the gate-level description is still the
// gateLib one and the RTL description still the aLib one -- so the declaration
// order is the only thing this map turned.
TEST(DefaultLibraryBinding, DeclarationOrderAloneDecidesWhichAdderIsBound) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d,
                                 "library rtlLib top.v;\n"
                                 "library gateLib adder.vg;\n"
                                 "library aLib adder.*;\n"));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "adder", "aLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = BoundChild(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "gateLib");
}

// The rule is the one that governs when no configuration settles the binding,
// and what settles a binding is the configuration a design is elaborated from.
// A configuration whose default clause names gateLib alone is written beside
// the design and the design is then elaborated from its cell name rather than
// from that configuration, so the search order is still the map's declaration
// order: the adder binds the aLib description the configuration's own library
// list would have excluded.
TEST(DefaultLibraryBinding, DesignElaboratedFromACellNameUsesDeclarationOrder) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));
  const std::string kConfigCell =
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  default liblist gateLib;\n"
      "endconfig\n";
  auto cfg_file = tmp.Write("cfg.sv", kConfigCell);
  ASSERT_TRUE(d.ParseFile(cfg_file, kConfigCell));
  ASSERT_EQ(d.unit->configs.size(), 1u);

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = BoundChild(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "aLib");
}

// The rule is about searching the libraries, not about instantiation alone, so
// it settles the cell that tops the design as well as the cells beneath it.
// Two files describe a cell named top and the map sends them to two libraries;
// the design is elaborated from that cell name with no configuration naming a
// library for it, so the first declared library holding a top supplies it. The
// map declares gateLib first here and the RTL file is parsed first, so neither
// the file order nor a preference for an RTL description could produce the
// answer.
TEST(DefaultLibraryBinding, TopCellComesFromFirstDeclaredLibraryHoldingIt) {
  ScratchDir tmp;
  MappedDesign d;
  const std::string kTopCell = "module top;\nendmodule\n";
  auto map_file = tmp.Write("lib.map",
                            "library gateLib top.vg;\n"
                            "library rtlLib top.v;\n");
  auto gate = tmp.Write("top.vg", kTopCell);
  auto rtl = tmp.Write("top.v", kTopCell);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.ParseFile(rtl, kTopCell));
  ASSERT_TRUE(d.ParseFile(gate, kTopCell));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "top", "rtlLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->library, "gateLib");
}

// A cell is a design element of any kind the language declares, so the search
// order settles an interface instance on the same terms as a module instance.
// Both libraries holding a bus are searched in the order the map declares them
// and the file describing the aLib bus is parsed last, so the earlier
// declaration is what carries the binding.
TEST(DefaultLibraryBinding, InterfaceCellIsSearchedInDeclarationOrderToo) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(
      BuildTwoFileCellDesign(tmp, d,
                             {.base = "bus",
                              .cell = "interface bus;\nendinterface\n",
                              .top = "module top;\n  bus b();\nendmodule\n"}));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "bus", "gateLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = BoundChild(top, "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "aLib");
}

// And for a program, the next kind of design element a library holds as a cell.
// The two descriptions differ in nothing but the file name that earned each its
// library, so the instance taking the aLib one can only come from aLib being
// declared ahead of gateLib.
TEST(DefaultLibraryBinding, ProgramCellIsSearchedInDeclarationOrderToo) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(
      BuildTwoFileCellDesign(tmp, d,
                             {.base = "pgm",
                              .cell = "program pgm;\nendprogram\n",
                              .top = "module top;\n  pgm p();\nendmodule\n"}));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "pgm", "gateLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = BoundChild(top, "p");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "aLib");
}

// And for a checker, the remaining kind of design element the search reaches.
TEST(DefaultLibraryBinding, CheckerCellIsSearchedInDeclarationOrderToo) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(
      BuildTwoFileCellDesign(tmp, d,
                             {.base = "chk",
                              .cell = "checker chk;\nendchecker\n",
                              .top = "module top;\n  chk c1();\nendmodule\n"}));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "chk", "gateLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = BoundChild(top, "c1");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "chk");
  EXPECT_EQ(bound->library, "aLib");
}

// The libraries searched are the ones the map declares, so a description whose
// file matched no file path specification takes no position in that order and
// is reached only once every declared library has been passed over. The extra
// file here describes an adder and is parsed before either mapped adder, so an
// implementation searching the descriptions in the order it read them would
// answer with the unmapped one.
TEST(DefaultLibraryBinding, UndeclaredLibraryIsSearchedAfterTheDeclaredOnes) {
  ScratchDir tmp;
  MappedDesign d;
  auto map_file = tmp.Write("lib.map", kExampleMap);
  auto spare = tmp.Write("spare.sv", kAdderFile);
  auto gate = tmp.Write("adder.vg", kAdderFile);
  auto rtl = tmp.Write("adder.v", kAdderFile);
  auto top_file = tmp.Write("top.v", kTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.ParseFile(spare, kAdderFile));
  ASSERT_TRUE(d.ParseFile(gate, kAdderFile));
  ASSERT_TRUE(d.ParseFile(rtl, kAdderFile));
  ASSERT_TRUE(d.ParseFile(top_file, kTopFile));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "adder", "work"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = BoundChild(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "aLib");
}

// A primitive is a cell, so it takes the name where its library is searched
// first: the map puts the primitive in aLib and the module in gateLib, aLib is
// declared ahead of gateLib, and the instantiation is taken as an instance of
// the primitive -- which leaves the module uninstantiated, so the topping cell
// holds no bound child at all.
TEST(DefaultLibraryBinding, PrimitiveInAnEarlierLibraryTakesTheName) {
  ScratchDir tmp;
  MappedDesign d;
  auto map_file = tmp.Write("lib.map",
                            "library rtlLib top.v;\n"
                            "library aLib w.v;\n"
                            "library gateLib w.vg;\n");
  auto gate = tmp.Write("w.vg", kWidgetModuleFile);
  auto rtl = tmp.Write("w.v", kWidgetPrimitiveFile);
  auto top_file = tmp.Write("top.v", kWidgetTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.ParseFile(gate, kWidgetModuleFile));
  ASSERT_TRUE(d.ParseFile(rtl, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.ParseFile(top_file, kWidgetTopFile));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "w", "gateLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->children.empty());
}

// And the other way round: with the module in aLib and the primitive in
// gateLib, the search reaches the module first, so the instantiation is an
// instance of it and binds the aLib description. A primitive of the name held
// by a library searched later does not take the name from it.
TEST(DefaultLibraryBinding, ModuleInAnEarlierLibraryKeepsTheNameFromPrimitive) {
  ScratchDir tmp;
  MappedDesign d;
  auto map_file = tmp.Write("lib.map",
                            "library rtlLib top.v;\n"
                            "library aLib w.v;\n"
                            "library gateLib w.vg;\n");
  auto gate = tmp.Write("w.vg", kWidgetPrimitiveFile);
  auto rtl = tmp.Write("w.v", kWidgetModuleFile);
  auto top_file = tmp.Write("top.v", kWidgetTopFile);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.ParseFile(gate, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.ParseFile(rtl, kWidgetModuleFile));
  ASSERT_TRUE(d.ParseFile(top_file, kWidgetTopFile));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "w", "gateLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* bound = BoundChild(top, "u");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "aLib");
}

// Which primitive the other kinds are measured against is the one the search
// reaches first, not the one that happened to be parsed first. Three libraries
// hold a primitive named w and a fourth holds a module of that name, and the
// module's library is searched before two of the three primitives but after the
// first. The primitive parsed first is the one in the last-searched library, so
// measuring against it would hand the name to the module; measuring against the
// first-searched one leaves the name with the primitive, and the topping cell
// holds no bound child.
TEST(DefaultLibraryBinding, NearestPrimitiveIsWhatOtherKindsAreMeasuredBy) {
  ScratchDir tmp;
  MappedDesign d;
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
  ASSERT_TRUE(d.ParseFile(last, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.ParseFile(first, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.ParseFile(middle, kWidgetPrimitiveFile));
  ASSERT_TRUE(d.ParseFile(module_file, kWidgetModuleFile));
  ASSERT_TRUE(d.ParseFile(top_file, kWidgetTopFile));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "w", "libB"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->children.empty());
}

// The order a library takes is the one its first declaration gives it, so
// naming a library again further down the map adds files to it without moving
// it. rtlLib is declared first and named a second time after aLib, and the file
// the second declaration adds describes an adder, so rtlLib now holds one. Its
// first position is what makes that description answer where the same map
// without the second declaration gave the aLib one.
TEST(DefaultLibraryBinding, LibraryNamedTwiceKeepsItsFirstPosition) {
  ScratchDir tmp;
  MappedDesign d;
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
  ASSERT_TRUE(d.ParseFile(gate, kAdderFile));
  ASSERT_TRUE(d.ParseFile(rtl, kAdderFile));
  ASSERT_TRUE(d.ParseFile(extra, kAdderOnlyFile));
  ASSERT_TRUE(d.ParseFile(top_file, kTopFile));
  ASSERT_TRUE(UnitHoldsCell(d.unit, "adder", "aLib"));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_FALSE(d.diag.HasErrors());
  ASSERT_NE(top, nullptr);
  auto* a1 = BoundChild(top, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "rtlLib");
}

// The nearest input the rule has to turn away: an instance naming a cell that
// no declared library holds. Searching every library in declaration order ends
// with nothing found, so the instance is reported and left unbound rather than
// filled in from some library the search never named.
TEST(DefaultLibraryBinding, InstanceOfACellNoLibraryHoldsIsLeftUnbound) {
  ScratchDir tmp;
  MappedDesign d;
  const std::string kTopCell = "module top;\n  subtractor s1();\nendmodule\n";
  auto map_file = tmp.Write("lib.map", kExampleMap);
  auto top_file = tmp.Write("top.v", kTopCell);
  ASSERT_TRUE(d.map.LoadMapFile(map_file));
  ASSERT_TRUE(d.ParseFile(top_file, kTopCell));

  auto* top = SoleTop(ElaborateUnderMapOrder(d, "top"));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(d.diag.HasErrors());
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

// The same refusal at the design root, the other position the search settles.
// Every declared library is searched for the named cell and none holds one, so
// the elaboration reports the name and yields no design rather than topping it
// with a cell out of some library the order never covered.
TEST(DefaultLibraryBinding, RootCellNoLibraryHoldsYieldsNoDesign) {
  ScratchDir tmp;
  MappedDesign d;
  ASSERT_TRUE(BuildExampleDesign(tmp, d, kExampleMap));

  auto* design = ElaborateUnderMapOrder(d, "subtractor");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(d.diag.HasErrors());
}

}  // namespace
