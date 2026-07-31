// Tests for IEEE 1800-2023 §33.8.1 "Using the command line to control library
// searching".
//
// The subclause states two rules, both conditioned on no configuration being
// in force:
//
//   Claim 1. A tool provides a way of naming a library search order on its
//   command line, and the order so named takes the place of the default order
//   the library map file's declarations establish.
//
//   Claim 2. What that command line carries is library names and nothing
//   else. Whatever each named library holds is settled by the map file, so a
//   name is a name of a library and never a definition of one.
//
// The subclause's note recommends spelling the mechanism "-L <library_name>",
// which is what src/main.cpp accepts; the note is a recommendation rather than
// a rule, so what the tests below hold to is the order itself.
//
// The rule is applied at the elaborator stage. The order an invocation is to
// use is what LibraryMap::ResolveSearchOrder (src/parser/library_map.cpp)
// yields from the names the command line gave and the declarations the map
// holds, and it decides a binding through
// Elaborator::SetLibraryDeclarationOrder (src/elaborator/elaborator.cpp) and
// PickByLibraryOrder (src/elaborator/elaborator_resolve.cpp). Rejecting an
// entry that is no library name is LibraryMap::IsLibraryName's work, and
// src/main.cpp stops a run over one rather than searching an order nobody
// asked for.
//
// An order ranks libraries; it does not choose which of them exist. A library
// the command line leaves unnamed is therefore searched after every library it
// named rather than dropped -- that a library list can exclude a library
// outright is a configuration's doing (§33.6.2) and not a search order's --
// and it is searched in the position its declaration gave it, since a command
// line that did not name it said nothing about where it ranks and the map file
// is what answers where nothing else does. What
// it ranks is a cell rather than a module, so the tests below run the order
// over a design element of another kind, and over a primitive besides -- a
// primitive is reached by a search of its own that reads the same order, which
// makes it a second piece of production code to observe rather than a second
// spelling of the first.
//
// What the rule consumes comes from this pass's dependency. The order it
// overrides, the library names it may use and the descriptions each of those
// libraries holds are all read out of a real lib.map, and §33.3.1.1 is what
// decides which library a command-line name is naming wherever two
// specifications cover one file. The shared map below leans on that twice
// over: a wildcard and an explicit file name compete for the gate-level file,
// and a later test has a directory specification and a file name compete for
// it instead. Every test therefore writes the map and the sources to disk,
// loads the map, parses each file and tags it through the map, and elaborates
// the assembled unit. No test writes a library onto a cell of its own accord.

#include <gtest/gtest.h>

#include <cstddef>
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

// The library map these tests bind against. rtlLib is declared first, aLib
// second and gateLib last, so an order nobody overrode answers aLib for a cell
// aLib and gateLib both hold. The aLib specification reaches adder.vg through
// its wildcard and the gateLib one names that file outright, so which library
// holds the gate-level description is decided by the map rather than by the
// declaration order, and a test may turn one without turning the other.
constexpr const char* kExampleMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib adder.vg;\n";

// The same map with the last library named in a way that uses the whole of the
// identifier alphabet -- a digit and a dollar sign after the opening letter --
// for the tests that ask which command-line entries are library names.
constexpr const char* kDollarNameMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gate$Lib2 adder.vg;\n";

// top.v: the cell topping the design instantiates the adder that two libraries
// describe and the m that only one of them does, so one elaboration reads back
// both what a named library won and what an unnamed one still supplied.
constexpr const char* kTopFile =
    "module top;\n"
    "  adder a1();\n"
    "  m u1();\n"
    "endmodule\n";

// adder.v: the RTL description, and the only description of m anywhere in the
// design. It reaches aLib through the map's wildcard specification.
constexpr const char* kAdderRtlFile =
    "module adder;\n"
    "endmodule\n"
    "module m;\n"
    "endmodule\n";

// adder.vg: the gate-level description of the same adder. Nothing distinguishes
// it from the RTL adder except the library the map's explicit specification
// earned it, so a binding that names one of them names it for that reason.
constexpr const char* kAdderGateFile =
    "module adder;\n"
    "endmodule\n";

// A configuration binding the same design, for the antecedent both rules carry:
// they hold where no configuration is in force. Its default clause names aLib,
// which is what a command-line order naming gateLib would otherwise settle
// differently. The file it is written to matches no specification in the map,
// so no library holds the configuration and it supplies no cell of its own.
constexpr const char* kConfigFile =
    "config cfg;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib;\n"
    "endconfig\n";

// A configuration with no default clause, for the other shape the antecedent
// takes. Nothing in it names a library list, so what settles the search under
// it is the rule that an instance takes the library its parent came from --
// still the configuration deciding, and still not the command line.
constexpr const char* kNoDefaultConfigFile =
    "config cfg;\n"
    "  design rtlLib.top;\n"
    "endconfig\n";

// A map whose topping library is filled by two specifications at once, so it
// holds a description of the adder beside the topping cell. The second
// specification is the one that reaches the extra file, which is how a
// declaration naming several file paths gets exercised alongside the rule
// under test.
constexpr const char* kTopLibraryAdderMap =
    "library rtlLib top.v, rtladder.v;\n"
    "library aLib adder.*;\n"
    "library gateLib adder.vg;\n";

// The example map with the gate-level library named the way an identifier may
// open where no letter does.
constexpr const char* kUnderscoreNameMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library _gate_lib adder.vg;\n";

// A map reaching its two adder libraries through the two lowest tiers a file
// path specification has: dirLib names a directory and so covers everything
// written under it, while fileLib names one file in that directory outright.
// Both specifications match adder.vg, and it is the precedence between the
// tiers that leaves that description in fileLib.
constexpr const char* kSubdirectoryMap =
    "library rtlLib top.v;\n"
    "library dirLib sub/;\n"
    "library fileLib sub/adder.vg;\n";

// A map sending the module description of one cell to aLib and the primitive
// description of that same cell to gateLib.
constexpr const char* kWidgetMap =
    "library rtlLib top.v;\n"
    "library aLib w.v;\n"
    "library gateLib w.vg;\n";

// The same two libraries with the primitive's declared ahead of the module's,
// so the order the map alone establishes hands the name to the primitive.
constexpr const char* kWidgetPrimitiveFirstMap =
    "library rtlLib top.v;\n"
    "library gateLib w.vg;\n"
    "library aLib w.v;\n";

// The two descriptions of that cell. They take the same terminals, so one
// instantiation reads as an instance of either and which library the search
// reaches first is what decides between them.
constexpr const char* kWidgetModule =
    "module w(output y, input a);\n"
    "  assign y = ~a;\n"
    "endmodule\n";
constexpr const char* kWidgetPrimitive =
    "primitive w(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";
constexpr const char* kWidgetTop =
    "module top;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  w u(y, a);\n"
    "endmodule\n";

// A source file as the fixture writes it out: the name it is written under,
// which is what the map's file path specifications match against, and the text
// it holds.
struct SourceFile {
  std::string name;
  std::string text;
};

// One compilation unit assembled out of several source files, the way a tool
// handed several files assembles one. Each file is parsed on its own and its
// cells are written into whichever library its path earns from the map, so
// every library named in an expectation below was established by a map read
// off disk.
struct LibraryDesign {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap map;
  CompilationUnit* unit = nullptr;
};

// Folds the cells a further file described into the unit being assembled. The
// designs below are made of modules and one configuration, so those are the
// two kinds of declaration there is anything to carry across.
void MergeUnit(LibraryDesign& d, CompilationUnit* cu) {
  if (d.unit == nullptr) {
    d.unit = cu;
    return;
  }
  d.unit->modules.insert(d.unit->modules.end(), cu->modules.begin(),
                         cu->modules.end());
  d.unit->configs.insert(d.unit->configs.end(), cu->configs.begin(),
                         cu->configs.end());
}

// Writes `map_text` and `files` into the scratch directory, loads the map, and
// parses each file into one unit tagged through that map. Returns false when
// the map does not load or a file does not parse.
bool Assemble(ScratchDir& tmp, LibraryDesign& d, const std::string& map_text,
              const std::vector<SourceFile>& files) {
  auto map_path = tmp.Write("lib.map", map_text);
  std::vector<fs::path> paths;
  paths.reserve(files.size());
  for (const auto& file : files) {
    paths.push_back(tmp.Write(file.name, file.text));
  }
  if (!d.map.LoadMapFile(map_path)) return false;

  for (size_t i = 0; i < files.size(); ++i) {
    auto fid = d.mgr.AddFile(paths[i].string(), files[i].text);
    Lexer lexer(d.mgr.FileContent(fid), fid, d.diag);
    Parser parser(lexer, d.arena, d.diag);
    auto* cu = parser.Parse();
    if (cu == nullptr || d.diag.HasErrors()) return false;
    d.map.TagCompilationUnit(*cu, paths[i].string());
    MergeUnit(d, cu);
  }
  return d.unit != nullptr;
}

// The three source descriptions every test binds against, with the gate-level
// one written and parsed ahead of the RTL one. A tool binding whichever
// description it met first would answer the gate-level library everywhere, so
// the parse order cannot be what produces an expectation of aLib.
std::vector<SourceFile> DesignFiles() {
  std::vector<SourceFile> files;
  files.push_back({"adder.vg", kAdderGateFile});
  files.push_back({"adder.v", kAdderRtlFile});
  files.push_back({"top.v", kTopFile});
  return files;
}

// Builds that design under `map_text`.
bool BuildDesign(ScratchDir& tmp, LibraryDesign& d,
                 const std::string& map_text) {
  return Assemble(tmp, d, map_text, DesignFiles());
}

// The same design with the configuration parsed alongside it.
bool BuildConfiguredDesign(ScratchDir& tmp, LibraryDesign& d) {
  auto files = DesignFiles();
  files.push_back({"cfg.sv", kConfigFile});
  return Assemble(tmp, d, kExampleMap, files);
}

// The module and the primitive description of one cell, with the primitive
// written and parsed first so neither answer can come from the parse order.
std::vector<SourceFile> WidgetFiles() {
  std::vector<SourceFile> files;
  files.push_back({"w.vg", kWidgetPrimitive});
  files.push_back({"w.v", kWidgetModule});
  files.push_back({"top.v", kWidgetTop});
  return files;
}

// One cell described in two files, for the tests that vary the kind of design
// element a library holds it as. `base` names the pair -- base.v, which the
// map sends to aLib, and base.vg, which it sends to gateLib -- `cell` is the
// description written into both of them, and `top` describes the cell
// instantiating it once.
struct CellKindFixture {
  std::string base;
  std::string cell;
  std::string top;
};

// Builds that pair under a map declaring rtlLib, then aLib, then gateLib, with
// the gate-level file parsed first. The declaration order answers aLib, so a
// test naming gateLib on the command line and reading gateLib back has read
// back the command line's doing whatever kind of element the cell is.
bool BuildCellKindDesign(ScratchDir& tmp, LibraryDesign& d,
                         const CellKindFixture& c) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library aLib " + c.base + ".v;\n";
  map_text += "library gateLib " + c.base + ".vg;\n";
  std::vector<SourceFile> files;
  files.push_back({c.base + ".vg", c.cell});
  files.push_back({c.base + ".v", c.cell});
  files.push_back({"top.v", c.top});
  return Assemble(tmp, d, map_text, files);
}

// Elaborates the cell `top` names under exactly `order`, which is the search
// order an invocation that named the libraries it wanted is left with.
RtlirDesign* ElaborateWithOrder(LibraryDesign& d, std::string_view top,
                                std::vector<std::string> order) {
  Elaborator elab(d.arena, d.diag, d.unit);
  elab.SetLibraryDeclarationOrder(std::move(order));
  return elab.Elaborate(top);
}

// Elaborates the assembled configuration under that same order, so what the
// configuration decides can be told apart from what the order would have.
RtlirDesign* ElaborateConfigWithOrder(LibraryDesign& d,
                                      std::vector<std::string> order) {
  Elaborator elab(d.arena, d.diag, d.unit);
  elab.SetLibraryDeclarationOrder(std::move(order));
  return elab.Elaborate(d.unit->configs.front());
}

// The one top module an elaborated design holds, or nullptr when it holds none
// or holds several.
RtlirModule* SoleTopOf(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return nullptr;
  return design->top_modules[0];
}

// The cell bound to the instance `inst` names under that top module, or
// nullptr when the design holds no such binding.
RtlirModule* BoundCell(RtlirDesign* design, std::string_view inst) {
  auto* top = SoleTopOf(design);
  if (top == nullptr) return nullptr;
  for (const auto& child : top->children) {
    if (child.inst_name == inst) return child.resolved;
  }
  return nullptr;
}

// The library that bound cell came from. Answers an empty view where there is
// no such binding, which no expectation below accepts.
std::string_view BoundLibrary(RtlirDesign* design, std::string_view inst) {
  auto* cell = BoundCell(design, inst);
  return cell == nullptr ? std::string_view{} : cell->library;
}

// The names an order holds, in the positions it holds them, as one word per
// position. An order is what these tests compare, and reading it back whole
// says which libraries reached it as well as how they were ranked.
std::string Joined(const std::vector<std::string>& order) {
  std::string out;
  for (const auto& name : order) {
    if (!out.empty()) out += ' ';
    out += name;
  }
  return out;
}

// Whether any declaration in `decls` answers to `cell` and lives in `library`.
// Every kind of design element carries both, so one walk serves them all.
template <typename Decls>
bool AnyDeclIn(const Decls& decls, std::string_view cell,
               std::string_view library) {
  for (const auto* decl : decls) {
    if (decl->name == cell && decl->library == library) return true;
  }
  return false;
}

// Whether the assembled unit holds a description of `cell` in `library`, over
// every kind of design element a library holds as a cell. A test claiming a
// search reached one library rather than another first states that the other
// one held a description to be passed over, so a design that never held it
// cannot pass for one whose description lost the search.
bool UnitHoldsCellIn(const CompilationUnit* unit, std::string_view cell,
                     std::string_view library) {
  return AnyDeclIn(unit->modules, cell, library) ||
         AnyDeclIn(unit->interfaces, cell, library) ||
         AnyDeclIn(unit->programs, cell, library) ||
         AnyDeclIn(unit->checkers, cell, library) ||
         AnyDeclIn(unit->udps, cell, library);
}

// Claim 1: with nothing named on the command line, the order is the one the
// map file's declarations establish, and the adder binds the description held
// by the first declared library that holds one.
TEST(CommandLineLibrarySearchOrder,
     NoCommandLineOrderLeavesTheMapDeclarationOrderStanding) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "gateLib"));

  auto order = d.map.ResolveSearchOrder({});
  EXPECT_EQ(Joined(order), "rtlLib aLib gateLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "aLib");
}

// Claim 1: an order the command line names takes the place of the declaration
// order rather than being appended to it, so a library the map declares last
// binds the adder once the command line puts it first.
TEST(CommandLineLibrarySearchOrder,
     CommandLineOrderReplacesTheMapDeclarationOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "aLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib", "aLib", "rtlLib"});
  EXPECT_EQ(Joined(order), "gateLib aLib rtlLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

// Claim 1: naming one library orders that library ahead of the rest; it does
// not narrow the search to it. The adder goes to the library that was named,
// and the m only the unnamed aLib describes is still found there. The two
// libraries the command line passed over follow it in the order the map
// declares them, which is the order of the whole list read back here.
TEST(CommandLineLibrarySearchOrder,
     LibraryLeftOffTheCommandLineOrderIsStillSearched) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "m", "aLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  auto* design = ElaborateWithOrder(d, "top", order);
  EXPECT_EQ(BoundLibrary(design, "a1"), "gateLib");
  EXPECT_EQ(BoundLibrary(design, "u1"), "aLib");
}

// Claim 1 where the ranking of the passed-over libraries is the whole answer.
// The command line names the one library holding no adder at all, so which
// description binds is settled entirely among the two it did not name -- and
// they are ranked by their declarations, aLib ahead of gateLib. The
// gate-level file is written and parsed first, so a search leaving the two
// tied and taking whichever description it met first would answer gateLib.
// Nothing about the design or the map is what makes the answer aLib: the same
// two libraries answer gateLib in the test above, where the command line
// named one of them.
TEST(CommandLineLibrarySearchOrder,
     UnnamedLibrariesKeepTheirDeclaredOrderBehindTheNamedOnes) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "gateLib"));
  ASSERT_FALSE(UnitHoldsCellIn(d.unit, "adder", "rtlLib"));

  auto order = d.map.ResolveSearchOrder({"rtlLib"});
  EXPECT_EQ(Joined(order), "rtlLib aLib gateLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "aLib");
}

// Claim 2: a name is a name only, and what the library so named holds is the
// map file's to say. A name no declaration in the map introduced therefore
// ranks a library holding nothing, and the search passes over it to the next
// name rather than stopping there.
TEST(CommandLineLibrarySearchOrder,
     CommandLineNameNoDeclarationIntroducedRanksAnEmptyLibrary) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));
  EXPECT_FALSE(UnitHoldsCellIn(d.unit, "adder", "phantomLib"));

  auto order = d.map.ResolveSearchOrder({"phantomLib", "gateLib", "aLib"});
  EXPECT_EQ(Joined(order), "phantomLib gateLib aLib rtlLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

// Claim 1: what the command line names is an order, so a library named twice
// occupies one position in it -- the earlier one, which is the position a
// search reaches.
TEST(CommandLineLibrarySearchOrder,
     LibraryNamedTwiceOnTheCommandLineIsRankedOnce) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));

  auto order = d.map.ResolveSearchOrder({"gateLib", "aLib", "gateLib"});
  EXPECT_EQ(Joined(order), "gateLib aLib rtlLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

// Claim 2, negative: the closest thing to a library name that is not one is a
// source file the library holds. It names no library, so it is reported and
// left out, and the names given beside it still make the order.
TEST(CommandLineLibrarySearchOrder,
     CommandLineEntryNamingAFileIsNotALibraryName) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kExampleMap));

  std::vector<std::string> errors;
  auto order = d.map.ResolveSearchOrder({"adder.vg", "gateLib"}, &errors);
  ASSERT_EQ(errors.size(), 1u);
  EXPECT_NE(errors[0].find("adder.vg"), std::string::npos);
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"), "gateLib");
}

// Claim 2, negative: the other shapes a command line might carry where a
// library name belongs -- an absolute path, a wildcard, a word opening with a
// digit, nothing at all, and a word broken by a character no identifier holds.
// None of them is a name, so none of them reaches the order.
TEST(CommandLineLibrarySearchOrder, NoEntryButALibraryNameEntersTheOrder) {
  std::vector<std::string> entries;
  entries.push_back("/proj/lib1/*.v");
  entries.push_back("*.v");
  entries.push_back("2lib");
  entries.push_back("");
  entries.push_back("a-lib");

  LibraryMap map;
  std::vector<std::string> errors;
  auto order = map.ResolveSearchOrder(entries, &errors);
  EXPECT_TRUE(order.empty());
  EXPECT_EQ(errors.size(), entries.size());
}

// Claim 2: an identifier runs on past its opening letter through digits and
// dollar signs, so a library the map declares under such a name is a library
// the command line can name.
TEST(CommandLineLibrarySearchOrder,
     LibraryNameWithDigitAndDollarSignIsALibraryName) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kDollarNameMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "gate$Lib2"));

  std::vector<std::string> errors;
  auto order = d.map.ResolveSearchOrder({"gate$Lib2"}, &errors);
  EXPECT_TRUE(errors.empty());
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"),
            "gate$Lib2");
}

// Both claims hold in the absence of a configuration (§33.8). With one in
// force its default clause settles the search, and the adder binds the library
// that clause names rather than the one the command line put first.
TEST(CommandLineLibrarySearchOrder,
     ConfigurationInForceSettlesWhatTheCommandLineOrderWould) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildConfiguredDesign(tmp, d));
  ASSERT_FALSE(d.unit->configs.empty());

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  EXPECT_EQ(BoundLibrary(ElaborateConfigWithOrder(d, order), "a1"), "aLib");
}

// The antecedent again, for a configuration that names no library list at all.
// Naming none is not the same as naming nothing: the instance takes the
// library its parent cell came from, and the topping library holds an adder of
// its own here, so that is what binds. The command line named a different
// library first and the configuration is what keeps it from deciding.
TEST(CommandLineLibrarySearchOrder,
     ConfigurationWithNoDefaultClauseOverridesTheCommandLineOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  auto files = DesignFiles();
  files.push_back({"rtladder.v", kAdderGateFile});
  files.push_back({"cfg.sv", kNoDefaultConfigFile});
  ASSERT_TRUE(Assemble(tmp, d, kTopLibraryAdderMap, files));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "rtlLib"));
  ASSERT_FALSE(d.unit->configs.empty());

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  EXPECT_EQ(Joined(order), "gateLib rtlLib aLib");
  EXPECT_EQ(BoundLibrary(ElaborateConfigWithOrder(d, order), "a1"), "rtlLib");
}

// Claim 2: an identifier may open with an underscore where no letter opens it,
// so a library the map declares under such a name is one the command line can
// name. Nothing else about the map moved, so the binding turning to that
// library is the command line's doing.
TEST(CommandLineLibrarySearchOrder,
     LibraryNameOpeningWithAnUnderscoreIsALibraryName) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(BuildDesign(tmp, d, kUnderscoreNameMap));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "_gate_lib"));

  std::vector<std::string> errors;
  auto order = d.map.ResolveSearchOrder({"_gate_lib"}, &errors);
  EXPECT_TRUE(errors.empty());
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "a1"),
            "_gate_lib");
}

// Claim 1b end to end over §33.3.1.1, the dependency that decides which
// library a command-line name is naming. Two specifications cover the
// gate-level file -- a directory that holds it and its own file name -- and
// the file name is the more specific of the two, so that description lands in
// fileLib. Naming fileLib first is then what binds it, and the test answers
// dirLib if either the precedence between the two tiers or the command-line
// order were to go the other way.
TEST(CommandLineLibrarySearchOrder,
     CellPlacedByTheDirectoryTierIsRankedByTheCommandLine) {
  ScratchDir tmp;
  LibraryDesign d;
  std::vector<SourceFile> files;
  files.push_back({"sub/adder.vg", kAdderGateFile});
  files.push_back({"sub/adder.v", kAdderRtlFile});
  files.push_back({"top.v", kTopFile});
  ASSERT_TRUE(Assemble(tmp, d, kSubdirectoryMap, files));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "fileLib"));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "adder", "dirLib"));

  auto order = d.map.ResolveSearchOrder({"fileLib", "dirLib"});
  EXPECT_EQ(Joined(order), "fileLib dirLib rtlLib");
  auto* design = ElaborateWithOrder(d, "top", order);
  EXPECT_EQ(BoundLibrary(design, "a1"), "fileLib");
  EXPECT_EQ(BoundLibrary(design, "u1"), "dirLib");
}

// Claim 1b over a design element of another kind, since what the order ranks
// is a cell rather than a module. One kind stands for the rest that reach the
// same search: an interface, a program and a checker are gathered into one
// candidate list and ranked by one comparison that reads none of them, so a
// second and third kind here would repeat this test rather than add to it.
// Which kinds a library holds as a cell is settled by §33.6.1.
TEST(CommandLineLibrarySearchOrder,
     InterfaceCellIsRankedByTheCommandLineOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  CellKindFixture c;
  c.base = "bus";
  c.cell = "interface bus;\nendinterface\n";
  c.top = "module top;\n  bus b();\nendmodule\n";
  ASSERT_TRUE(BuildCellKindDesign(tmp, d, c));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "bus", "aLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  auto* bound = BoundCell(ElaborateWithOrder(d, "top", order), "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "gateLib");
}

// A primitive is a cell a library holds as much as a module is, and the search
// that reaches one is a second piece of production code reading the order.
// An instance keeps no record of which library supplied a primitive, so what
// is read back is whether the name reached the primitive at all: reaching it
// leaves the instantiation an instance of a primitive and the topping cell
// with no bound child, where reaching the module would leave one. The map puts
// the module in the library declared earlier, so only the command line naming
// the primitive's library can turn the name over to it.
TEST(CommandLineLibrarySearchOrder,
     PrimitiveCellIsRankedByTheCommandLineOrder) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(Assemble(tmp, d, kWidgetMap, WidgetFiles()));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "w", "aLib"));
  ASSERT_TRUE(UnitHoldsCellIn(d.unit, "w", "gateLib"));

  auto order = d.map.ResolveSearchOrder({"gateLib"});
  auto* top = SoleTopOf(ElaborateWithOrder(d, "top", order));
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->children.empty());
}

// The other way round, so the empty answer above reads as the search arriving
// somewhere rather than as an elaboration that bound nothing. Here the map
// declares the primitive's library first, so the order it establishes would
// hand the name to the primitive and leave no bound child; naming the module's
// library on the command line is the only thing that gives the name back.
TEST(CommandLineLibrarySearchOrder,
     CommandLineOrderCanGiveTheNameBackToTheModule) {
  ScratchDir tmp;
  LibraryDesign d;
  ASSERT_TRUE(Assemble(tmp, d, kWidgetPrimitiveFirstMap, WidgetFiles()));
  ASSERT_EQ(Joined(d.map.ResolveSearchOrder({})), "rtlLib gateLib aLib");

  auto order = d.map.ResolveSearchOrder({"aLib"});
  EXPECT_EQ(Joined(order), "aLib rtlLib gateLib");
  EXPECT_EQ(BoundLibrary(ElaborateWithOrder(d, "top", order), "u"), "aLib");
}

}  // namespace
