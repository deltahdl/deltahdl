// Tests for IEEE 1800-2023 §33.2.1 "Library notation". A library is a named
// collection of cells; a cell is a design element -- a module, a primitive, an
// interface, a program, a package or a configuration -- and it carries the name
// of the design element it was made from. The symbolic notation names such a
// cell, optionally qualified by the library holding it, and the ':config'
// extension is what names a configuration where a module or a primitive already
// answers to the name.
//
// Each test builds its cells from real design-element declarations and drives
// the config elaboration that resolves the notation, so the name being resolved
// is the one a declaration actually put in a library.
#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

// The libraries the design elements of a test source are written into, listed
// in declaration order per kind. A library holds cells of every design element
// kind, so a source can place a module, an interface, a program, a primitive
// and a checker alike.
struct CellLibraries {
  // Each list starts empty, so a test names the kinds its source describes and
  // says nothing about the kinds it does not.
  std::vector<std::string_view> modules = {};
  std::vector<std::string_view> interfaces = {};
  std::vector<std::string_view> programs = {};
  std::vector<std::string_view> primitives = {};
  std::vector<std::string_view> checkers = {};
};

// Parses a source, writes its design elements into the named libraries and
// elaborates the first configuration it declares.
struct ConfigElab {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  RtlirDesign* design = nullptr;

  void Run(const std::string& src, const CellLibraries& libs);
};

// Assigns each library name to the design element declared at the same position
// in `decls`. A source names no more libraries than it declares elements, so a
// mismatch is the test's own mistake and is reported as one. Declarations of
// every design element kind carry a library, so the kind is left to the caller.
template <typename Decls>
void WriteCellsToLibraries(const Decls& decls,
                           const std::vector<std::string_view>& libs) {
  ASSERT_LE(libs.size(), decls.size());
  for (size_t i = 0; i < libs.size(); ++i) decls[i]->library = libs[i];
}

void ConfigElab::Run(const std::string& src, const CellLibraries& libs) {
  auto fid = mgr.AddFile("<test>", src);
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());
  WriteCellsToLibraries(cu->modules, libs.modules);
  WriteCellsToLibraries(cu->interfaces, libs.interfaces);
  WriteCellsToLibraries(cu->programs, libs.programs);
  WriteCellsToLibraries(cu->udps, libs.primitives);
  WriteCellsToLibraries(cu->checkers, libs.checkers);
  ASSERT_FALSE(cu->configs.empty());
  Elaborator elab(arena, diag, cu);
  design = elab.Elaborate(cu->configs[0]);
}

// The design's single top module, or nullptr when the design did not come out
// with that shape. Returning nullptr leaves the caller's ASSERT to report it
// rather than indexing an empty vector, which would take the whole executable
// down along with the tests it had not reached yet.
RtlirModule* OnlyTop(const RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1) return nullptr;
  return design->top_modules[0];
}

// Two cells named `leaf`, which two libraries each hold a copy of, and a cell
// `mid` instantiating one of them. Which library the leaf comes from is what
// shows whose library list governed that part of the hierarchy.
constexpr const char* kLeafAndMidCells =
    "module leaf; endmodule\n"
    "module leaf; endmodule\n"
    "module mid; leaf lf(); endmodule\n";

// The instance `top.m` handed to the name `midcfg`, which the configuration
// `midcfg` also answers to. Its design statement names a different cell
// (lib1.mid) and its library list a different library (libB) from the outer
// configuration's, so which of the two the name reached is visible in what
// top.m and its own child bind to.
constexpr const char* kPlainUseOfMidcfg =
    "module top; mid m(); endmodule\n"
    "config cfg;\n"
    "  design top;\n"
    "  default liblist libA;\n"
    "  instance top.m use lib1.midcfg;\n"
    "endconfig\n"
    "config midcfg;\n"
    "  design lib1.mid;\n"
    "  default liblist libB;\n"
    "endconfig\n";

// The same, with the extension written out.
constexpr const char* kConfigUseOfMidcfg =
    "module top; mid m(); endmodule\n"
    "config cfg;\n"
    "  design top;\n"
    "  default liblist libA;\n"
    "  instance top.m use lib1.midcfg:config;\n"
    "endconfig\n"
    "config midcfg;\n"
    "  design lib1.mid;\n"
    "  default liblist libB;\n"
    "endconfig\n";

// A primitive answering to the name `midcfg`.
constexpr const char* kPrimitiveMidcfg =
    "primitive midcfg(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";

// Checks the shape that arises only when the name reached configuration
// `midcfg`: that configuration's design statement puts cell `mid` of lib1 under
// the selected instance, and its own library list (libB) then governs that
// cell's subtree, where the outer configuration's list (libA) would otherwise
// have chosen the libA copy of `leaf`.
void ExpectInstanceHandedToMidcfg(const RtlirDesign* design) {
  auto* top = OnlyTop(design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "mid");
  EXPECT_EQ(bound->library, "lib1");
  ASSERT_EQ(bound->children.size(), 1u);
  auto* leaf = bound->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(leaf->library, "libB");
}

// The extension is optional: where no design element other than a configuration
// answers to the name, the plain name names that configuration.
TEST(LibraryCellNotation, PlainNameNamesConfigWhenNoCellSharesIt) {
  ConfigElab e;
  e.Run(std::string(kLeafAndMidCells) + kPlainUseOfMidcfg,
        {.modules = {"libA", "libB", "lib1", "libTop"}});
  ExpectInstanceHandedToMidcfg(e.design);
}

// A module written into a library under the same name is what the plain name
// names, so the configuration is left unreached: the instance binds the module
// `midcfg` itself, and the outer configuration's library list keeps governing
// the subtree.
TEST(LibraryCellNotation, PlainNameNamesModuleSharingConfigName) {
  ConfigElab e;
  e.Run(std::string(kLeafAndMidCells) +
            "module midcfg; leaf lf(); endmodule\n" + kPlainUseOfMidcfg,
        {.modules = {"libA", "libB", "lib1", "lib1", "libTop"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "midcfg");
  ASSERT_EQ(bound->children.size(), 1u);
  auto* leaf = bound->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(leaf->library, "libA");
}

// A primitive of the name settles the plain name just as a module does. The
// configuration goes unreached, so the instance is left with nothing of the
// configuration's design statement under it -- had the name reached the
// configuration, cell lib1.mid would be bound here.
TEST(LibraryCellNotation, PlainNameNamesPrimitiveSharingConfigName) {
  ConfigElab e;
  e.Run(
      std::string(kLeafAndMidCells) + kPrimitiveMidcfg + kPlainUseOfMidcfg,
      {.modules = {"libA", "libB", "lib1", "libTop"}, .primitives = {"lib1"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

// Which is what the extension is for: with a primitive answering to the name,
// the configuration is reachable only by writing ':config' explicitly, and the
// same source that left the instance unbound above now hands it over.
TEST(LibraryCellNotation, ConfigExtensionNamesConfigSharingPrimitiveName) {
  ConfigElab e;
  e.Run(
      std::string(kLeafAndMidCells) + kPrimitiveMidcfg + kConfigUseOfMidcfg,
      {.modules = {"libA", "libB", "lib1", "libTop"}, .primitives = {"lib1"}});
  ExpectInstanceHandedToMidcfg(e.design);
}

// A cell is a design element of any kind the language declares, not a module
// alone, so a library-qualified name reaches the interface a library holds.
// Both copies of `bus` are declared alike and differ only in their library, so
// binding the libB copy where the configuration's own library list names libA
// can only come from the notation naming that library's cell.
TEST(LibraryCellNotation, QualifiedNameNamesInterfaceCell) {
  ConfigElab e;
  e.Run(
      "interface bus; endinterface\n"
      "interface bus; endinterface\n"
      "module top; bus b(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell bus use libB.bus;\n"
      "endconfig\n",
      {.modules = {"libTop"}, .interfaces = {"libA", "libB"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "libB");
}

// The same for a program, the other design element kind a library holds beside
// modules and interfaces.
TEST(LibraryCellNotation, QualifiedNameNamesProgramCell) {
  ConfigElab e;
  e.Run(
      "program pgm; endprogram\n"
      "program pgm; endprogram\n"
      "module top; pgm p(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell pgm use libB.pgm;\n"
      "endconfig\n",
      {.modules = {"libTop"}, .programs = {"libA", "libB"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->library, "libB");
}

// A cell's name is the name of the design element it was made from, so the
// notation names `widget` -- what the declaration is called -- and the clause
// then picks the libB copy over the libA one the configuration's library list
// would otherwise have chosen.
TEST(LibraryCellNotation, CellNameIsTheDeclaredDesignElementName) {
  ConfigElab e;
  e.Run(
      "module widget; endmodule\n"
      "module widget; endmodule\n"
      "module top; widget u(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell widget liblist libB;\n"
      "endconfig\n",
      {.modules = {"libA", "libB", "libTop"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

// The name an instance is given is not a cell name: nothing was written into a
// library under it. The same clause naming `u`, the instance of `widget`,
// selects no cell, so the configuration's library list still decides and the
// libA copy binds.
TEST(LibraryCellNotation, InstanceNameIsNotACellName) {
  ConfigElab e;
  e.Run(
      "module widget; endmodule\n"
      "module widget; endmodule\n"
      "module top; widget u(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell u liblist libB;\n"
      "endconfig\n",
      {.modules = {"libA", "libB", "libTop"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libA");
}

// A checker is a design element too, so a library holds one as a cell and the
// notation reaches it. Here a module and a checker answer to `chk` in different
// libraries, and naming libB's cell reaches the checker where the library list
// would otherwise have taken libA's module.
TEST(LibraryCellNotation, QualifiedNameNamesCheckerCell) {
  ConfigElab e;
  e.Run(
      "module chk; endmodule\n"
      "checker chk; endchecker\n"
      "module top; chk c1(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell chk use libB.chk;\n"
      "endconfig\n",
      {.modules = {"libA", "libTop"}, .checkers = {"libB"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

// An extern module declaration states a module's ports without defining the
// module, so nothing was written into a library under that name and the
// notation reaches no cell: the sole thing answering to `gate` in libB is the
// prototype, and the selected instance is left unbound.
TEST(LibraryCellNotation, ExternPrototypeIsNotACell) {
  ConfigElab e;
  e.Run(
      "extern module gate(input a);\n"
      "module sub; endmodule\n"
      "module top; sub u(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell sub use libB.gate;\n"
      "endconfig\n",
      {.modules = {"libB", "libA", "libTop"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

// The library part of the notation names where to look, and a library holding
// no cell of that name yields nothing -- a copy of the name in some other
// library is not a substitute. Both libA and libB hold a `widget`, and naming
// libC still leaves the instance unbound.
TEST(LibraryCellNotation, QualifiedNameFindsNothingOutsideItsLibrary) {
  ConfigElab e;
  e.Run(
      "module widget; endmodule\n"
      "module widget; endmodule\n"
      "module top; widget u(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell widget use libC.widget;\n"
      "endconfig\n",
      {.modules = {"libA", "libB", "libTop"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

// A cell of any design element kind carries its declaration's name, so an
// interface is selected by what its declaration is called. The clause names
// `bus` and moves the binding to libB's copy, which the configuration's own
// library list would not have chosen.
TEST(LibraryCellNotation, InterfaceCellSelectedByItsDeclaredName) {
  ConfigElab e;
  e.Run(
      "interface bus; endinterface\n"
      "interface bus; endinterface\n"
      "module top; bus b(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell bus liblist libB;\n"
      "endconfig\n",
      {.modules = {"libTop"}, .interfaces = {"libA", "libB"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->library, "libB");
}

// An interface sharing the configuration's name settles the plain name the way
// a module or a primitive does -- what makes the extension necessary is a
// design element answering to the name, whichever kind it is. The instance
// binds the interface, so the configuration went unreached.
TEST(LibraryCellNotation, PlainNameNamesInterfaceSharingConfigName) {
  ConfigElab e;
  e.Run(
      std::string(kLeafAndMidCells) + "interface midcfg; endinterface\n" +
          kPlainUseOfMidcfg,
      {.modules = {"libA", "libB", "lib1", "libTop"}, .interfaces = {"lib1"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_interface);
  EXPECT_EQ(bound->name, "midcfg");
}

// And for a checker, the remaining kind a library holds as a cell. The
// instance binds the checker, so the plain name stopped at it rather than
// carrying on to the configuration of that name.
TEST(LibraryCellNotation, PlainNameNamesCheckerSharingConfigName) {
  ConfigElab e;
  e.Run(std::string(kLeafAndMidCells) + "checker midcfg; endchecker\n" +
            kPlainUseOfMidcfg,
        {.modules = {"libA", "libB", "lib1", "libTop"}, .checkers = {"lib1"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "midcfg");
  EXPECT_EQ(bound->library, "lib1");
}

// The same for a program sharing the configuration's name.
TEST(LibraryCellNotation, PlainNameNamesProgramSharingConfigName) {
  ConfigElab e;
  e.Run(std::string(kLeafAndMidCells) + "program midcfg; endprogram\n" +
            kPlainUseOfMidcfg,
        {.modules = {"libA", "libB", "lib1", "libTop"}, .programs = {"lib1"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_program);
  EXPECT_EQ(bound->name, "midcfg");
}

// The rule holds in the other position the notation appears in, a design
// statement: `dtop` names both a module and a configuration, and with no
// extension written the statement names the module, which elaborates as the
// design's top.
TEST(LibraryCellNotation, DesignStatementNameSharedWithConfigNamesTheCell) {
  ConfigElab e;
  e.Run(
      "module dtop; endmodule\n"
      "config cfg;\n"
      "  design lib1.dtop;\n"
      "endconfig\n"
      "config dtop;\n"
      "  design lib1.dtop;\n"
      "endconfig\n",
      {.modules = {"lib1"}});
  auto* top = OnlyTop(e.design);
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->name, "dtop");
  EXPECT_FALSE(e.diag.HasErrors());
}

// And a name only a configuration answers to reaches no cell at all, so a
// design statement written with it names nothing that can be elaborated and is
// rejected.
TEST(LibraryCellNotation, DesignStatementNamingOnlyAConfigRejected) {
  ConfigElab e;
  e.Run(
      "module tcell; endmodule\n"
      "config cfg;\n"
      "  design lib1.only;\n"
      "endconfig\n"
      "config only;\n"
      "  design lib1.tcell;\n"
      "endconfig\n",
      {.modules = {"lib1"}});
  EXPECT_TRUE(
      ReportedError(e.diag.Diagnostics(),
                    "config 'cfg' design statement names configuration 'only'",
                    3, "33.4.1.1"));
}

}  // namespace
