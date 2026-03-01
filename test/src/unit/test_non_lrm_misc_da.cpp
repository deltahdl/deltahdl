// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string& src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using ConfigParseTest = ProgramTestParse;

ParseResult ParseLibrary(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.ParseLibraryText();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection28, Sec28_12_TimingCheckHold) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(ParserSection28, Sec28_12_TimingCheckSetuphold) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, 3, 2);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  ASSERT_EQ(si->timing_check.limits.size(), 2u);
}

TEST(ParserSection28, Sec28_12_TimingCheckRecovery) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recovery(posedge clk, rst, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecovery);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "rst");
}

TEST(ParserSection28, Sec28_12_TimingCheckRemoval) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $removal(negedge rst, posedge clk, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRemoval);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "rst");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
}

TEST(ParserSection28, Sec28_12_TimingCheckRecrem) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 5, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecrem);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "rst");
  ASSERT_EQ(si->timing_check.limits.size(), 2u);
}

TEST(ParserSection28, Sec28_12_TimingCheckWidth) {
  auto sp = ParseSpecifySingle(
      "module m(input clk);\n"
      "  specify\n"
      "    $width(posedge clk, 50);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(ParserSection28, Sec28_12_TimingCheckPeriod) {
  auto sp = ParseSpecifySingle(
      "module m(input clk);\n"
      "  specify\n"
      "    $period(posedge clk, 100);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
}

TEST(ParserSection28, Sec28_12_TimingCheckSkew) {
  auto sp = ParseSpecifySingle(
      "module m(input clk1, clk2);\n"
      "  specify\n"
      "    $skew(posedge clk1, posedge clk2, 20);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk1");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk2");
}

TEST(ParserSection28, Sec28_12_TimingCheckWithNotifier) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  reg notif_reg;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10, notif_reg);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  EXPECT_EQ(sp.sole_item->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(sp.sole_item->timing_check.notifier, "notif_reg");
}

TEST(ParserSection28, Sec28_12_TimingCheckWithEdges) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(negedge d, posedge clk, 8);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "d");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
}

// =============================================================================
// §31.7 Conditioned events
// =============================================================================
TEST_F(SpecifyTest, ConditionedSetup) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& clr, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc.ref_terminal.name, "data");
  EXPECT_NE(tc.ref_condition, nullptr);
}

TEST_F(SpecifyTest, ConditionedHoldBothSignals) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kHold);
  EXPECT_NE(tc.ref_condition, nullptr);
  EXPECT_NE(tc.data_condition, nullptr);
}

// =============================================================================
// §31.9 Extended $setuphold arguments
// =============================================================================
TEST_F(SpecifyTest, SetupholdWithDelayedSignals) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, -10, 20, ntfr, , , dCLK, dD);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(tc.notifier, "ntfr");
  EXPECT_EQ(tc.delayed_ref, "dCLK");
  EXPECT_EQ(tc.delayed_data, "dD");
}

// =============================================================================
// §33 Configuration declarations
// =============================================================================
TEST_F(ConfigParseTest, BasicConfig) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithEndLabel) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
    endconfig : cfg
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithDefaultClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist lib1 lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithInstanceClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      instance top.u1 liblist lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithCellClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell top use lib.other;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigCoexistsWithModule) {
  auto* unit = Parse(R"(
    module m;
    endmodule
    config cfg;
      design lib.top;
    endconfig
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, MultipleConfigs) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib.top1;
    endconfig
    config cfg2;
      design lib.top2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 2u);
  EXPECT_EQ(unit->configs[0]->name, "cfg1");
  EXPECT_EQ(unit->configs[1]->name, "cfg2");
}

// =============================================================================
// A.1.1 library_text ::= { library_description }
// =============================================================================
// Empty library text produces an empty CompilationUnit.
TEST(LibraryText, EmptyInput) {
  auto r = ParseLibrary("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
  EXPECT_TRUE(r.cu->lib_includes.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

// A null library description (bare semicolon) is valid.
TEST(LibraryText, NullDescription) {
  auto r = ParseLibrary(";\n;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
}

// =============================================================================
// A.1.1 library_declaration ::=
//   library library_identifier file_path_spec
//   { , file_path_spec } [ -incdir file_path_spec { , file_path_spec } ] ;
// =============================================================================
// Basic library declaration with a single file path.
TEST(LibraryText, BasicLibraryDecl) {
  auto r = ParseLibrary("library mylib /proj/rtl/top.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "mylib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/top.v");
}

// Library declaration with wildcard file path.
TEST(LibraryText, LibraryDeclWildcard) {
  auto r = ParseLibrary("library rtlLib *.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "*.v");
}

// Library declaration with dot-slash relative path.
TEST(LibraryText, LibraryDeclDotSlash) {
  auto r = ParseLibrary("library gateLib ./*.vg;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./*.vg");
}

// Library declaration with multiple file paths.
TEST(LibraryText, LibraryDeclMultiplePaths) {
  auto r = ParseLibrary("library lib /a/*.v, /b/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/a/*.v");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[1], "/b/*.v");
}

// Library declaration with -incdir clause.
TEST(LibraryText, LibraryDeclWithIncdir) {
  auto r = ParseLibrary("library lib /proj/*.v -incdir /proj/inc;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/*.v");
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/proj/inc");
}

// Library declaration with multiple -incdir paths.
TEST(LibraryText, LibraryDeclMultipleIncdir) {
  auto r = ParseLibrary("library lib /proj/*.v -incdir /inc1, /inc2, /inc3;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 3u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/inc1");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[1], "/inc2");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[2], "/inc3");
}

// Library declaration with both multiple file paths and multiple -incdir.
TEST(LibraryText, LibraryDeclFullForm) {
  auto r = ParseLibrary(
      "library rtlLib /proj/rtl/*.v, /proj/extra/*.v\n"
      "  -incdir /proj/inc, /proj/common;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/*.v");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[1], "/proj/extra/*.v");
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/proj/inc");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[1], "/proj/common");
}

// Library declaration with hierarchical wildcard path (...).
TEST(LibraryText, LibraryDeclHierarchicalWildcard) {
  auto r = ParseLibrary("library deepLib .../a.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], ".../a.v");
}

// Library declaration with single-char wildcard (?).
TEST(LibraryText, LibraryDeclQuestionWildcard) {
  auto r = ParseLibrary("library lib ./rtl/?.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./rtl/?.v");
}

// Library declaration with directory-only path (trailing slash).
TEST(LibraryText, LibraryDeclDirectoryPath) {
  auto r = ParseLibrary("library lib /proj/rtl/;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/");
}

}  // namespace
