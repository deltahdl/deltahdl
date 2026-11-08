#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "helpers_config_reports.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct CellLibraries {
  std::vector<std::string_view> modules = {};
  std::vector<std::string_view> interfaces = {};
  std::vector<std::string_view> programs = {};
  std::vector<std::string_view> primitives = {};
  std::vector<std::string_view> checkers = {};
};

struct ConfigElab {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  RtlirDesign* design = nullptr;

  void Run(const std::string& src, const CellLibraries& libs);
};

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
  PlaceConfigsWithTheirTops(cu);
  Elaborator elab(arena, diag, cu);
  design = elab.Elaborate(cu->configs[0]);
}

RtlirModule* OnlyTop(const RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1) return nullptr;
  return design->top_modules[0];
}

constexpr const char* kLeafAndMidCells =
    "module leaf; endmodule\n"
    "module leaf; endmodule\n"
    "module mid; leaf lf(); endmodule\n";

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

constexpr const char* kPrimitiveMidcfg =
    "primitive midcfg(output y, input a);\n"
    "  table 0 : 1 ; 1 : 0 ; endtable\n"
    "endprimitive\n";

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

TEST(LibraryCellNotation, PlainNameNamesConfigWhenNoCellSharesIt) {
  ConfigElab e;
  e.Run(std::string(kLeafAndMidCells) + kPlainUseOfMidcfg,
        {.modules = {"libA", "libB", "lib1", "libTop"}});
  ExpectInstanceHandedToMidcfg(e.design);
}

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

TEST(LibraryCellNotation, PlainNameNamesPrimitiveSharingConfigName) {
  ConfigElab e;
  e.Run(
      std::string(kLeafAndMidCells) + kPrimitiveMidcfg + kPlainUseOfMidcfg,
      {.modules = {"libA", "libB", "lib1", "libTop"}, .primitives = {"lib1"}});
  EXPECT_TRUE(ReportedError(e.diag.Diagnostics(),
                            "primitive 'midcfg' takes 2 terminal(s) but this "
                            "instance connects 0",
                            7, "29.8"));
}

TEST(LibraryCellNotation, ConfigExtensionNamesConfigSharingPrimitiveName) {
  ConfigElab e;
  e.Run(
      std::string(kLeafAndMidCells) + kPrimitiveMidcfg + kConfigUseOfMidcfg,
      {.modules = {"libA", "libB", "lib1", "libTop"}, .primitives = {"lib1"}});
  ExpectInstanceHandedToMidcfg(e.design);
}

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
