#include <gtest/gtest.h>
#include <unistd.h>

#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "helpers_separate_units.h"
#include "lexer/lexer.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

namespace {

namespace fs = std::filesystem;

TEST(CompilationUnitPreprocessing, IncludeBecomesPartOfCU) {
  auto r = ParseWithPreprocessor(
      "`define MY_CONST 42\n"
      "module m;\n"
      "  localparam C = `MY_CONST;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(CompilationUnitPreprocessing, GloballyVisibleDesignElements) {
  auto r = ParseWithPreprocessor(
      "package pkg; endpackage\n"
      "interface intf; endinterface\n"
      "program prog; endprogram\n"
      "module mod; endmodule\n"
      "primitive udp_and(output o, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

TEST(CompilationUnitPreprocessing, CuScopeClassDecl) {
  auto r = ParseWithPreprocessor(
      "class my_class;\n"
      "  int x;\n"
      "endclass\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "my_class");
}

static const ModuleItem* FindItemByKindAndName(
    const std::vector<ModuleItem*>& items, ModuleItemKind kind,
    const std::string& name) {
  for (const auto* item : items)
    if (item->kind == kind && item->name == name) return item;
  return nullptr;
}

TEST(CompilationUnitPreprocessing, NameResolutionOrder) {
  auto r = ParseWithPreprocessor(
      "function int helper(int x); return x; endfunction\n"
      "module m;\n"
      "  function int helper(int x); return x * 2; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");

  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_NE(FindItemByKindAndName(r.cu->modules[0]->items,
                                  ModuleItemKind::kFunctionDecl, "helper"),
            nullptr);
}

TEST(CompilationUnitPreprocessing, CuScopeCannotBeImported) {
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  EXPECT_TRUE(r.cu->cu_items.empty());
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(CompilationUnitPreprocessing, HierRefFromCUScope) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  module_a u1();\n"
      "endmodule\n"
      "module module_a;\n"
      "  logic sig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

TEST(CompilationUnitPreprocessing, TypeSharingViaCUScope) {
  auto r = ParseWithPreprocessor(
      "class shared_type;\n"
      "  int value;\n"
      "endclass\n"
      "module m1;\n"
      "  shared_type obj;\n"
      "endmodule\n"
      "module m2;\n"
      "  shared_type obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

TEST(CompilationUnitPreprocessing, CheckerAtCUScope) {
  auto r = ParseWithPreprocessor(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

TEST(CompilationUnitPreprocessing, CuScopeTypedefStored) {
  auto r = ParseWithPreprocessor(
      "typedef logic [7:0] byte_t;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(r.cu->cu_items[0]->name, "byte_t");
}

TEST(CompilationUnitPreprocessing, CuScopeLocalparamStored) {
  auto r = ParseWithPreprocessor(
      "localparam int WIDTH = 8;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "WIDTH");
}

TEST(CompilationUnitPreprocessing, CuScopeImportStored) {
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "import pkg::*;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(CompilationUnitPreprocessing, CuScopeVarDeclStored) {
  auto r = ParseWithPreprocessor(
      "int global_counter;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "global_counter");
}

TEST(CompilationUnitPreprocessing, DollarUnitScopeResolution) {
  auto r = ParseWithPreprocessor(
      "bit b;\n"
      "task t;\n"
      "  int b;\n"
      "  b = 5 + $unit::b;\n"
      "endtask\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CompilationUnitPreprocessing, ForwardRefOnlyDefinedNames) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin end\n"
      "endmodule\n"
      "int later_var;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "later_var");
}

TEST(CompilationUnitPreprocessing, EmptySourceText) {
  auto r = ParseWithPreprocessor("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
}

TEST(CompilationUnitPreprocessing, UnitScopeDeclarations) {
  auto r = ParseWithPreprocessor(
      "function automatic int helper(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "task automatic global_task(input int v);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 2u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  EXPECT_EQ(r.cu->cu_items[1]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(r.cu->cu_items[1]->name, "global_task");
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(CompilationUnitPreprocessing, MultipleModules) {
  auto r = ParseWithPreprocessor(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(CompilationUnitPreprocessing, CuScopeItemWithMacroExpansion) {
  auto r = ParseWithPreprocessor(
      "`define DEFAULT_WIDTH 16\n"
      "localparam int WIDTH = `DEFAULT_WIDTH;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "WIDTH");
}

TEST(CompilationUnitPreprocessing, DirectiveDefinedBetweenModules) {
  auto r = ParseWithPreprocessor(
      "module m1; endmodule\n"
      "`define DEPTH 4\n"
      "module m2;\n"
      "  localparam D = `DEPTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

TEST(CompilationUnitPreprocessing, IncludeDirectiveContentBecomesPartOfCu) {
  fs::path dir = fs::temp_directory_path() /
                 ("delta_test_cu_include_" + std::to_string(getpid()));
  fs::create_directories(dir);
  std::ofstream(dir / "shared.svh")
      << "function int helper(int x); return x; endfunction\n";

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile((dir / "top.sv").string(),
                         "`include \"shared.svh\"\nmodule m; endmodule\n");
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();

  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 1u);
  EXPECT_EQ(cu->modules[0]->name, "m");
  ASSERT_EQ(cu->cu_items.size(), 1u);
  EXPECT_EQ(cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(cu->cu_items[0]->name, "helper");

  fs::remove_all(dir);
}

TEST(CompilationUnitPreprocessing,
     MacroDefinitionDoesNotCrossCompilationUnits) {
  SourceManager mgr_a;
  DiagEngine diag_a(mgr_a);
  auto fid_a =
      mgr_a.AddFile("<unit_a>", "`define WIDTH 8\nmodule a; endmodule\n");
  Preprocessor preproc_a(mgr_a, diag_a, {});
  (void)preproc_a.Preprocess(fid_a);

  SourceManager mgr_b;
  DiagEngine diag_b(mgr_b);
  auto fid_b = mgr_b.AddFile("<unit_b>",
                             "module b;\n"
                             "  localparam int W = `WIDTH;\n"
                             "endmodule\n");
  Preprocessor preproc_b(mgr_b, diag_b, {});
  auto pp_b = preproc_b.Preprocess(fid_b);
  EXPECT_TRUE(ReportedError(diag_b.Diagnostics(), "undefined macro 'WIDTH'", 2,
                            "22.5.1"));
  EXPECT_EQ(pp_b.find('8'), std::string::npos);
}

// Runs `src` through `pp` as one more source file, the way a driver hands it
// each file of the command line in turn.
static std::string PreprocessFile(const std::string& src, PreprocFixture& f,
                                  Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<file>", src);
  return pp.Preprocess(fid);
}

// §3.12.1: where each file is a compilation unit of its own, the directives one
// unit read do not affect another, so a macro the first file defines is
// undefined in the second once a new unit begins between them. Without the
// boundary the second file's usage would expand to 8.
TEST(CompilationUnitPreprocessing, NewUnitUndefinesTheEarlierUnitsMacros) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("`define WIDTH 8\nmodule a; endmodule\n", f, pp);
  pp.BeginCompilationUnit();
  auto out = PreprocessFile(
      "module b;\n"
      "  localparam int W = `WIDTH;\n"
      "endmodule\n",
      f, pp);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undefined macro 'WIDTH'", 2,
                            "22.5.1"));
  EXPECT_EQ(out.find('8'), std::string::npos);
}

// §3.12.1: a macro the command line defines is given to every unit, so one the
// first unit undefined is defined again in the next.
TEST(CompilationUnitPreprocessing, CommandLineDefineReachesEveryUnit) {
  PreprocFixture f;
  PreprocConfig config;
  config.defines.emplace_back("DEPTH", "4");
  Preprocessor pp(f.mgr, f.diag, config);
  PreprocessFile("`undef DEPTH\nmodule a; endmodule\n", f, pp);
  pp.BeginCompilationUnit();
  auto out = PreprocessFile("localparam int D = `DEPTH;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find('4'), std::string::npos);
}

// §3.12.1 with §22.7 and §22.8: the time scale and default net type one unit
// set are not in force in the next, while §3.14.3's global precision, the
// finest of every unit's, keeps what the first unit contributed.
TEST(CompilationUnitPreprocessing, NewUnitResetsDirectivesButKeepsPrecision) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile(
      "`timescale 1ns/1ps\n"
      "`default_nettype none\n"
      "`celldefine\n"
      "module a; endmodule\n",
      f, pp);
  pp.BeginCompilationUnit();
  EXPECT_FALSE(pp.HasTimescale());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
  EXPECT_FALSE(pp.InCelldefine());
  EXPECT_TRUE(pp.HasGlobalPrecision());
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

// §3.12.1 with §22.7: a directive applies to all the text after it in its
// compilation unit, so a `timescale the first file read governs a module the
// second file of the unit declares, while a module of the next unit takes
// none.
TEST(CompilationUnitPreprocessing, TimescaleReachesTheUnitsLaterFile) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("`timescale 1ns/1ps\nmodule a; endmodule\n", f, pp);
  PreprocessFile("module m;\n  initial #1;\nendmodule\n", f, pp);
  pp.BeginCompilationUnit();
  PreprocessFile("module z; endmodule\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& list = pp.ModuleDirectivesList();
  ASSERT_EQ(list.size(), 3u);
  EXPECT_EQ(list[1].module, "m");
  EXPECT_TRUE(list[1].has_timescale);
  EXPECT_EQ(list[1].timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(list[1].timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(list[2].module, "z");
  EXPECT_FALSE(list[2].has_timescale);
}

// The directive records of module a, declared after `directive` in one
// compilation unit, and of module b, declared in the next unit.
static std::vector<ModuleDirectives> RecordsAcrossUnits(
    const std::string& directive, PreprocFixture& f) {
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile(directive + "\nmodule a; endmodule\n", f, pp);
  pp.BeginCompilationUnit();
  PreprocessFile("module b; endmodule\n", f, pp);
  return pp.ModuleDirectivesList();
}

// §3.12.1 with §22.9: a directive of one compilation unit does not affect
// another, so the next unit's module leaves its unconnected input ports
// unpulled, while the module after `unconnected_drive in its own unit pulls
// them.
TEST(CompilationUnitPreprocessing, UnconnectedDriveStaysInItsUnit) {
  PreprocFixture f;
  auto list = RecordsAcrossUnits("`unconnected_drive pull1", f);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(list.size(), 2u);
  EXPECT_EQ(list[0].unconnected_drive, NetType::kTri1);
  EXPECT_EQ(list[1].unconnected_drive, NetType::kWire);
}

// §3.12.1 with Annex E.2: the next unit's trireg nets keep the infinite decay
// time, while those of the module after `default_decay_time in its own unit
// take the time it names.
TEST(CompilationUnitPreprocessing, DefaultDecayTimeStaysInItsUnit) {
  PreprocFixture f;
  auto list = RecordsAcrossUnits("`default_decay_time 100", f);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(list.size(), 2u);
  EXPECT_FALSE(list[0].decay_infinite);
  EXPECT_EQ(list[0].decay_ticks, 100u);
  EXPECT_TRUE(list[1].decay_infinite);
  EXPECT_EQ(list[1].decay_ticks, 0u);
}

// §3.12.1 with Annex E.3: the next unit's trireg nets keep the default charge
// strength, while those of the module after `default_trireg_strength in its
// own unit take the strength it names.
TEST(CompilationUnitPreprocessing, DefaultTriregStrengthStaysInItsUnit) {
  PreprocFixture f;
  auto list = RecordsAcrossUnits("`default_trireg_strength 30", f);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(list.size(), 2u);
  EXPECT_TRUE(list[0].has_strength);
  EXPECT_EQ(list[0].strength, 30u);
  EXPECT_FALSE(list[1].has_strength);
}

// §3.12.1 with Annex E.4 to E.7: the next unit's module keeps the delays as
// written, while the module after each delay mode directive in its own unit
// takes that directive's mode.
TEST(CompilationUnitPreprocessing, DelayModeStaysInItsUnit) {
  struct Mode {
    const char* directive;
    DelayModeDirective mode;
  };
  const Mode kModes[] = {
      {"`delay_mode_distributed", DelayModeDirective::kDistributed},
      {"`delay_mode_path", DelayModeDirective::kPath},
      {"`delay_mode_unit", DelayModeDirective::kUnit},
      {"`delay_mode_zero", DelayModeDirective::kZero},
  };
  for (const auto& written : kModes) {
    PreprocFixture f;
    auto list = RecordsAcrossUnits(written.directive, f);
    EXPECT_FALSE(f.diag.HasErrors()) << written.directive;
    ASSERT_EQ(list.size(), 2u) << written.directive;
    EXPECT_EQ(list[0].delay_mode, written.mode) << written.directive;
    EXPECT_EQ(list[1].delay_mode, DelayModeDirective::kNone)
        << written.directive;
  }
}

// A directory of this process's own holding the header h.svh with `text`.
static fs::path WriteHeader(const std::string& text) {
  fs::path dir = fs::temp_directory_path() /
                 ("delta_test_cu_header_" + std::to_string(getpid()));
  fs::create_directories(dir);
  std::ofstream(dir / "h.svh") << text;
  return dir;
}

// Preprocesses `srcs` with one preprocessor as the files of a run that makes
// each file a compilation unit of its own, each file standing in `dir` so that
// a quoted `include finds the header written there, and gives back each
// unit's text.
static std::vector<std::string> PreprocessUnits(
    const fs::path& dir, const std::vector<std::string>& srcs, ElabFixture& f) {
  Preprocessor pp(f.mgr, f.diag, {});
  std::vector<std::string> texts;
  for (const auto& src : srcs) {
    if (!texts.empty()) pp.BeginCompilationUnit();
    auto path = dir / ("unit" + std::to_string(texts.size()) + ".sv");
    texts.push_back(pp.Preprocess(f.mgr.AddFile(path.string(), src)));
  }
  return texts;
}

// Elaborates the units `texts` hold together, under the top module top.
static RtlirDesign* ElaborateTexts(const std::vector<std::string>& texts,
                                   ElabFixture& f) {
  Elaborator elab(f.arena, f.diag,
                  ParseUnitsApart(texts, f.mgr, f.arena, f.diag));
  auto* design = elab.Elaborate("top");
  f.has_errors = f.diag.HasErrors();
  return design;
}

// §3.12.1: the text an `include reads joins the compilation unit of the file
// that includes it, so where each file is a unit of its own, a typedef the
// header declares is no type a module of the other unit can name.
TEST(CompilationUnitPreprocessing, HeaderOfOneUnitStaysOutOfAnother) {
  fs::path dir = WriteHeader("typedef logic [3:0] t;\n");
  ElabFixture f;
  ElaborateTexts(PreprocessUnits(dir,
                                 {"`include \"h.svh\"\n"
                                  "module a; endmodule\n",
                                  "module top;\n"
                                  "  t v;\n"
                                  "endmodule\n"},
                                 f),
                 f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 't' does not precede", 2,
                            "6.18"));
  fs::remove_all(dir);
}

// §3.12.1: the nearest allowed form, a module of the including file's own
// unit, reads the header's typedef as a type of four bits.
TEST(CompilationUnitPreprocessing, HeaderDeclaresInTheIncludingUnit) {
  fs::path dir = WriteHeader("typedef logic [3:0] t;\n");
  ElabFixture f;
  auto* design = ElaborateTexts(PreprocessUnits(dir,
                                                {"`include \"h.svh\"\n"
                                                 "module top;\n"
                                                 "  t v;\n"
                                                 "endmodule\n",
                                                 "module b; endmodule\n"},
                                                f),
                                f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "top", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 4u);
  fs::remove_all(dir);
}

// §3.12.1 with §3.13: a header two units include declares its variable in
// each unit's scope once, so neither unit holds a redeclaration and each
// unit's module reads its own.
TEST(CompilationUnitPreprocessing, HeaderOfTwoUnitsDeclaresInEachOnce) {
  fs::path dir = WriteHeader("int g;\n");
  ElabFixture f;
  auto* design = ElaborateTexts(PreprocessUnits(dir,
                                                {"`include \"h.svh\"\n"
                                                 "module top;\n"
                                                 "  int x;\n"
                                                 "  initial x = g;\n"
                                                 "  child c();\n"
                                                 "endmodule\n",
                                                 "`include \"h.svh\"\n"
                                                 "module child;\n"
                                                 "  int y;\n"
                                                 "  initial y = g;\n"
                                                 "endmodule\n"},
                                                f),
                                f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  fs::remove_all(dir);
}

// §3.13: the nearest forbidden form, the header included twice by one unit,
// declares its variable twice in that unit's scope, and the second is the
// redeclaration.
TEST(CompilationUnitPreprocessing, HeaderIncludedTwiceByOneUnitRedeclares) {
  fs::path dir = WriteHeader("int g;\n");
  ElabFixture f;
  auto texts = PreprocessUnits(dir,
                               {"`include \"h.svh\"\n"
                                "`include \"h.svh\"\n"
                                "module top; endmodule\n"},
                               f);
  ASSERT_EQ(texts.size(), 1u);
  const std::string& text = texts[0];
  auto second = text.rfind("int g;");
  ASSERT_NE(second, std::string::npos);
  auto line = static_cast<uint32_t>(
      1 + std::count(text.begin(), text.begin() + second, '\n'));
  ElaborateTexts(texts, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'g' in compilation-unit scope",
                            line, "3.13"));
  fs::remove_all(dir);
}

// §3.12.1 with §22.11.1: a protect pragma keyword one unit wrote is back at its
// default in the next.
TEST(CompilationUnitPreprocessing, NewUnitRestoresPragmaKeywordDefaults) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("`pragma protect author=\"ada\"\n", f, pp);
  ASSERT_FALSE(pp.ProtectKeywords().ValueOf("author").defaulted);
  pp.BeginCompilationUnit();
  EXPECT_TRUE(pp.ProtectKeywords().ValueOf("author").defaulted);
}

// §3.12.1 with §22.14: a `begin_keywords region cannot run on into another
// unit, so one still open when its unit ends never meets its `end_keywords
// and is reported there.
TEST(CompilationUnitPreprocessing, KeywordRegionOpenAtUnitEndIsReported) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("`begin_keywords \"1364-2001\"\nmodule a; endmodule\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  pp.BeginCompilationUnit();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`begin_keywords without matching `end_keywords", 1,
                            "22.14"));
}

}  // namespace
