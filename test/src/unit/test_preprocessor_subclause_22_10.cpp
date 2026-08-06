#include <gtest/gtest.h>
#include <unistd.h>

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"

using namespace delta;
namespace fs = std::filesystem;

// §22.10 `celldefine and `endcelldefine. The subclause states six things:
//   C1  the two directives tag modules as cell modules,
//   C2  pairing a `celldefine with an `endcelldefine is advisable but not
//       required -- they are two independent directives,
//   C3  the most recent occurrence of either directive controls whether
//       modules are tagged,
//   C4  more than one pair may appear in a single source description,
//   C5  the directives may appear anywhere in the source description (keeping
//       them outside design elements is a recommendation, not a rule), and
//   C6  `resetall (§22.3) carries the effect of an `endcelldefine.
//
// Both directives are bare keywords with no operand, so the inputs that
// exercise them are source *positions* and *neighbouring constructs* rather
// than operand types: a module or macromodule header, a non-module design
// element, a header carried on the directive's own line, a header arriving
// through an `include, a header inside a conditional branch, and a longer
// macro name that merely begins with the keyword.
//
// The tag itself is only observable once a module header has actually been
// seen, so every test below builds its modules from real declaration syntax
// and reads the collected cell-module list back off the preprocessor.

namespace {

// A `celldefine region that spans an `include has to be observed across two
// real files, so the unit writes them to a scratch directory and lets the
// preprocessor resolve the include relative to the includer.
struct CelldefineUnitDir {
  fs::path dir;

  CelldefineUnitDir() {
    dir = fs::temp_directory_path() /
          ("delta_celldefine_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~CelldefineUnitDir() { fs::remove_all(dir); }

  void WriteFile(const std::string& rel_path, const std::string& content) {
    auto full = dir / rel_path;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
  }
};

std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                             Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

bool IsTaggedAsCell(const Preprocessor& pp, const std::string& name) {
  const auto& cells = pp.CellModuleNames();
  return std::find(cells.begin(), cells.end(), name) != cells.end();
}

std::string Squeeze(std::string_view text) {
  std::string out;
  for (char c : text) {
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r') continue;
    out.push_back(c);
  }
  return out;
}

// ---------------------------------------------------------------------------
// C1: the directives tag modules as cell modules.
// ---------------------------------------------------------------------------

TEST(CelldefinePreprocessing, TagsModuleDeclaredInRegion) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module cellmod;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "cellmod"));
}

// A macromodule is a module declaration too, so the region tags it the same
// way a plain module header is tagged.
TEST(CelldefinePreprocessing, TagsMacromoduleDeclaredInRegion) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "macromodule mm;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "mm"));
}

// The claim names no particular module header shape, so the parameter-port
// list and the ANSI port list of a realistic cell must not confuse the name
// the tag is recorded under.
TEST(CelldefinePreprocessing, TagsModuleWithParameterAndPortLists) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module and2 #(parameter int W = 1)\n"
      "            (input logic [W-1:0] a, b, output logic [W-1:0] y);\n"
      "  assign y = a & b;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "and2"));
}

// A lifetime keyword sits between the module keyword and the name, so the
// name the tag is filed under must be found past it.
TEST(CelldefinePreprocessing, TagsModuleWithExplicitLifetime) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module automatic auto_cell;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "auto_cell"));
}

// An escaped identifier is a legal module name, so a module that carries one
// is a module the region tags like any other.
TEST(CelldefinePreprocessing, TagsModuleWithEscapedName) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module \\cell$1 ;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module \\plain$2 ;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "\\cell$1"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "\\plain$2"));
}

// A module declaration may itself be nested in another module, and both are
// modules sitting inside the open region.
TEST(CelldefinePreprocessing, TagsNestedModuleDeclaration) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module outer_cell;\n"
      "  module inner_cell;\n"
      "  endmodule\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "outer_cell"));
  EXPECT_TRUE(IsTaggedAsCell(pp, "inner_cell"));
}

// The directive occupies no line of its own by rule, so a header sharing the
// directive's line is inside the region it just opened.
TEST(CelldefinePreprocessing, TagsModuleSharingTheDirectiveLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP(
      "`celldefine module sameline;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "sameline"));
  EXPECT_NE(out.find("module sameline;"), std::string::npos);
}

// A header that arrives through an `include is still part of the source
// description the open region covers.
TEST(CelldefinePreprocessing, TagsModuleArrivingThroughInclude) {
  CelldefineUnitDir tmp;
  tmp.WriteFile("cell_body.svh",
                "module included_cell;\n"
                "endmodule\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile(tmp.dir / "top.sv",
                           "`celldefine\n"
                           "`include \"cell_body.svh\"\n"
                           "`endcelldefine\n"
                           "module outside_cell;\n"
                           "endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "included_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "outside_cell"));
}

// The region an included file opens keeps controlling the file that included
// it, because a compilation unit is one source description.
TEST(CelldefinePreprocessing, RegionOpenedInsideIncludeReachesIncluder) {
  CelldefineUnitDir tmp;
  tmp.WriteFile("open_cell.svh", "`celldefine\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile(tmp.dir / "top.sv",
                           "`include \"open_cell.svh\"\n"
                           "module after_include;\n"
                           "endmodule\n"
                           "`endcelldefine\n"
                           "module after_end;\n"
                           "endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "after_include"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "after_end"));
}

// Negative for C1: the tag is for modules. A design element that is not a
// module is left alone even though it sits in the region -- the module in the
// same region witnesses that tagging was running at all.
TEST(CelldefinePreprocessing, DoesNotTagNonModuleDesignElements) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "interface iface;\n"
      "endinterface\n"
      "package pkg;\n"
      "endpackage\n"
      "program prog;\n"
      "endprogram\n"
      "primitive prim (output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "checker chk;\n"
      "endchecker\n"
      "config cfg;\n"
      "endconfig\n"
      "module witness_cell;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "witness_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "iface"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "pkg"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "prog"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "prim"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "chk"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "cfg"));
}

// Negative for C1: a module declared before any `celldefine has no directive
// in front of it to tag it.
TEST(CelldefinePreprocessing, DoesNotTagModuleDeclaredBeforeAnyDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "module plain;\n"
      "endmodule\n"
      "`celldefine\n"
      "module witness_cell;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "witness_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain"));
}

// ---------------------------------------------------------------------------
// C1 (negative, keyword recognition): the directives are the bare keywords
// `celldefine and `endcelldefine. A longer name that merely starts with one of
// them is a macro usage, not the directive.
// ---------------------------------------------------------------------------

TEST(CelldefinePreprocessing, LongerNameStartingWithCelldefineIsAMacro) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP(
      "`define celldefine_region wire tag_expanded;\n"
      "`celldefine_region\n"
      "module not_a_cell;\n"
      "endmodule\n"
      "`celldefine\n"
      "module witness_cell;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(Squeeze(out).find("wiretag_expanded;"), std::string::npos);
  EXPECT_TRUE(IsTaggedAsCell(pp, "witness_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "not_a_cell"));
}

TEST(CelldefinePreprocessing, LongerNameStartingWithEndcelldefineIsAMacro) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP(
      "`define endcelldefine_now wire done_expanded;\n"
      "`celldefine\n"
      "`endcelldefine_now\n"
      "module still_a_cell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module after_real_end;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(Squeeze(out).find("wiredone_expanded;"), std::string::npos);
  EXPECT_TRUE(IsTaggedAsCell(pp, "still_a_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "after_real_end"));
}

// ---------------------------------------------------------------------------
// C2: the two directives are independent; pairing is advisable, not required.
// ---------------------------------------------------------------------------

// An `endcelldefine with no `celldefine in front of it is not an error, and it
// leaves tagging off.
TEST(CelldefinePreprocessing, UnmatchedEndcelldefineIsHarmless) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`endcelldefine\n"
      "module plain;\n"
      "endmodule\n"
      "`celldefine\n"
      "module witness_cell;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "witness_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain"));
}

// A `celldefine that is never closed is not an error either: it simply keeps
// tagging to the end of the source description -- and it tags every module it
// reaches, not just the first one after the directive.
TEST(CelldefinePreprocessing, UnmatchedCelldefineKeepsTaggingToEnd) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module first_cell;\n"
      "endmodule\n"
      "module last_cell;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
  EXPECT_TRUE(IsTaggedAsCell(pp, "first_cell"));
  EXPECT_TRUE(IsTaggedAsCell(pp, "last_cell"));
}

// Because they are independent directives rather than a bracket pair, a
// repeated `celldefine does not nest: one `endcelldefine still ends tagging.
TEST(CelldefinePreprocessing, RepeatedCelldefineDoesNotNest) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "`celldefine\n"
      "module inner_cell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module after_one_end;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "inner_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "after_one_end"));
}

// The mirror image: a repeated `endcelldefine is harmless, and a later
// `celldefine still turns tagging back on.
TEST(CelldefinePreprocessing, RepeatedEndcelldefineIsHarmless) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module witness_cell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "`endcelldefine\n"
      "module plain;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "witness_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain"));
}

// ---------------------------------------------------------------------------
// C3: the most recent occurrence of either directive controls tagging.
// C4: a source description may hold more than one pair.
// ---------------------------------------------------------------------------

// More than one pair in a single source description, each pair controlling
// only the modules between its own two directives. This also carries the plain
// most-recent-occurrence pattern in both directions: cell_a shows an open
// region tags, plain_b shows the following `endcelldefine stops tagging, and
// cell_c shows a later `celldefine turns it back on.
TEST(CelldefinePreprocessing, MultiplePairsEachTagOnlyTheirOwnModules) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module cell_a;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module plain_b;\n"
      "endmodule\n"
      "`celldefine\n"
      "module cell_c;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module plain_d;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
  EXPECT_TRUE(IsTaggedAsCell(pp, "cell_a"));
  EXPECT_TRUE(IsTaggedAsCell(pp, "cell_c"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain_b"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain_d"));
}

// Nothing ties an occurrence to a line of its own, so both directives can land
// on one line. The one further right is the more recent, and it is the one that
// decides how the modules after that line are tagged.
TEST(CelldefinePreprocessing, LaterOfTwoDirectivesOnOneLineWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module first_cell;\n"
      "endmodule\n"
      "`endcelldefine `celldefine\n"
      "module second_cell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module plain;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "first_cell"));
  EXPECT_TRUE(IsTaggedAsCell(pp, "second_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain"));
}

// A source description is the whole compilation unit rather than one file, so
// the "more than one pair" allowance is satisfied by pairs sitting in separate
// files, each still controlling only its own modules.
TEST(CelldefinePreprocessing, MultiplePairsSpanningTwoFiles) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module a_cell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module a_plain;\n"
      "endmodule\n",
      f, pp);
  PreprocessWithPP(
      "`celldefine\n"
      "module b_cell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module b_plain;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
  EXPECT_TRUE(IsTaggedAsCell(pp, "a_cell"));
  EXPECT_TRUE(IsTaggedAsCell(pp, "b_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "a_plain"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "b_plain"));
}

// A source description spans every file of the compilation unit, so the most
// recent occurrence carries across a file boundary.
TEST(CelldefinePreprocessing, MostRecentOccurrenceCarriesAcrossFiles) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  EXPECT_FALSE(pp.InCelldefine());
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP(
      "module cross_file_cell;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(pp.InCelldefine());
  PreprocessWithPP(
      "module cross_file_plain;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "cross_file_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "cross_file_plain"));
}

// ---------------------------------------------------------------------------
// C5: the directives may appear anywhere in the source description. Placing
// one inside a design element is only discouraged, never an error -- unlike
// `timescale or `default_nettype, which this must not be lumped in with.
// ---------------------------------------------------------------------------

TEST(CelldefinePreprocessing, CelldefineInsideModuleIsAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "module t;\n"
      "`celldefine\n"
      "endmodule\n"
      "module after_t;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
  // The enclosing module was already declared when the directive occurred, so
  // the directive is not the most recent occurrence in front of it and the
  // region does not reach backwards to tag it.
  EXPECT_FALSE(IsTaggedAsCell(pp, "t"));
  EXPECT_TRUE(IsTaggedAsCell(pp, "after_t"));
}

TEST(CelldefinePreprocessing, EndcelldefineInsideModuleIsAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module t;\n"
      "`endcelldefine\n"
      "endmodule\n"
      "module after_t;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
  EXPECT_TRUE(IsTaggedAsCell(pp, "t"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "after_t"));
}

TEST(CelldefinePreprocessing, CelldefineInsideProceduralBlockIsAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "module t;\n"
      "  initial begin\n"
      "`celldefine\n"
      "    $display(\"body\");\n"
      "  end\n"
      "endmodule\n"
      "module after_t;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(IsTaggedAsCell(pp, "t"));
  EXPECT_TRUE(IsTaggedAsCell(pp, "after_t"));
}

TEST(CelldefinePreprocessing, CelldefineInsidePackageIsAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "package p;\n"
      "  localparam int K = 1;\n"
      "`celldefine\n"
      "endpackage\n"
      "module in_cell;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "in_cell"));
}

// The last line of a source file, with no terminating newline, is still a
// place the directive may appear.
TEST(CelldefinePreprocessing, CelldefineOnFinalLineWithoutNewline) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "module plain;\n"
      "endmodule\n"
      "`celldefine",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain"));
}

// Text excluded by a conditional is not part of the source description, so a
// directive sitting in a skipped branch never occurs.
TEST(CelldefinePreprocessing, CelldefineInSkippedBranchDoesNotOccur) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`ifdef NEVER_DEFINED\n"
      "`celldefine\n"
      "`endif\n"
      "module plain;\n"
      "endmodule\n"
      "`celldefine\n"
      "module witness_cell;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "witness_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "plain"));
}

TEST(CelldefinePreprocessing, EndcelldefineInSkippedBranchDoesNotOccur) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "`ifdef NEVER_DEFINED\n"
      "`endcelldefine\n"
      "`endif\n"
      "module still_a_cell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module after_real_end;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "still_a_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "after_real_end"));
}

// The directives themselves carry no text into the compiled source, but text
// following them on the same line is ordinary source and survives.
TEST(CelldefinePreprocessing, DirectivesLeaveNoTextBehind) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`celldefine\n`endcelldefine\n", f, pp);
  EXPECT_TRUE(Squeeze(out).empty());
}

TEST(CelldefinePreprocessing, TextAfterEndcelldefineSurvives) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`endcelldefine wire x;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire x;"), std::string::npos);
}

// ---------------------------------------------------------------------------
// C6: `resetall carries the effect of an `endcelldefine.
// ---------------------------------------------------------------------------

TEST(CelldefinePreprocessing, ResetallEndsTheCellRegion) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module witness_cell;\n"
      "endmodule\n"
      "`resetall\n"
      "module afterreset;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
  EXPECT_TRUE(IsTaggedAsCell(pp, "witness_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "afterreset"));
}

// `resetall only supplies the `endcelldefine effect; a `celldefine after it
// opens a fresh region as usual.
TEST(CelldefinePreprocessing, CelldefineAfterResetallOpensNewRegion) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "`resetall\n"
      "module afterreset;\n"
      "endmodule\n"
      "`celldefine\n"
      "module reopened_cell;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
  EXPECT_TRUE(IsTaggedAsCell(pp, "reopened_cell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "afterreset"));
}

}  // namespace
