// Tests for IEEE 1800-2023 §33.7 "Displaying library binding information".
//
// The subclause makes the binding a configuration produced observable from
// inside the running simulation, by two routes.
//
// The first is a format specifier. %l -- and %L, its other case -- substitutes
// the library and the cell bound to the module instance that contains the
// output command, written as one "library.cell" token. It is the binding
// counterpart of %m: it takes no argument of its own, it is available to the
// display task and to every other command that produces textual output, and
// the instance it reports is the one containing the call.
//
// The second is VPI. An object of type vpiModule carries the same information
// through three properties -- the library it was compiled into, the cell bound
// to the instance, and the configuration that decided that binding -- and all
// three are read as strings, the way vpiName and vpiFullName are.
//
// Both rules are applied at the simulator stage. The specifier is expanded by
// BuildInstanceBinding and TryNoArgScopeSpec (src/simulator/eval_format.cpp),
// which look the binding up by the running process's instance prefix;
// ScanFormatSpecifier (src/simulator/eval_systask.cpp) is what leaves the
// argument list alone for it. The value they read is recorded during lowering
// by RegisterInstanceKeyBinding (src/simulator/lowerer.cpp), called once for
// the top instance and once per child instance
// (src/simulator/lowerer_child.cpp), and held by RegisterInstanceBinding /
// FindInstanceBinding (src/simulator/sim_context.cpp). The VPI properties are
// resolved by VpiLibraryStr, VpiCellStr and VpiConfigStr and dispatched from
// the string switch VpiGetStrRawProperty (src/simulator/vpi_query.cpp); their
// constants live in src/simulator/vpi_constants.h and their storage in
// src/simulator/vpi_object.h.
//
// What the specifier reports is not something a test can state on its own: it
// is the verdict of the binding machinery this pass depends on. So every test
// of it below writes the §33.6 library map and source descriptions to disk,
// loads the map, parses each file through it, elaborates a real configuration
// -- a design statement, a default clause and an instance clause, the §33.5
// syntax -- and only then lowers the bound hierarchy and runs it, reading what
// $display wrote. The two adder descriptions are the same text in two files,
// so the library each instance reports can have come from the binding and from
// nothing else the test arranged; and the claim that an instance clause is
// what moved a binding is paired with the same design under the same default
// clause with that clause struck out, since a library the default clause would
// have answered anyway shows nothing. The instance names and the cell names
// are kept apart throughout (a1 and a2 instantiate adder, f1 instantiates m),
// so a specifier reporting the instance rather than the cell cannot pass.
//
// The specifier is then read in every position it can occupy. Each command
// that produces textual output gets its own case, including the two whose text
// is produced after the calling process has finished, which are written into an
// instantiated cell so a deferred expansion that lost the calling instance
// reports a binding the test rules out. A subroutine, a named block and a
// generate block each get a case pairing the specifier with the hierarchical
// name, since that pairing is what separates the scopes the name walks from the
// instance the binding belongs to. And because a cell is a design element of
// any kind, an interface instance and a program instance are read beside the
// module ones.
//
// The VPI properties have no such production path -- nothing in the tree
// builds VPI objects out of an elaborated design -- so they are read where
// they are written, on objects the test creates.

#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config_run.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

// The library map of §33.6. Both the aLib and the gateLib specification cover
// adder.vg and only gateLib's names that file outright, which is what leaves
// the gate-level descriptions in gateLib and the RTL ones in aLib. Nothing
// below writes a library onto a cell; every library named in an expectation
// was earned by a file path through this map.
constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

// top.v: the cell topping the design instantiates the adder twice, so a
// configuration can move one binding and leave its sibling alone. Its own
// output command reports the topping instance itself, which no instance clause
// below ever selects and which sits in a third library.
constexpr const char* kTopSource =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "  initial $display(\"[t %m %l]\");\n"
    "endmodule\n";

// adder.v and adder.vg: the RTL and the gate-level description of the same two
// cells. One text stands for both files, so the two differ in nothing a test
// could have arranged except the library their file names earned them. Each
// reports its binding in both cases of the specifier, and the cell inside it
// reports its own, a level further down.
constexpr const char* kAdderSource =
    "module adder;\n"
    "  m f1();\n"
    "  initial begin\n"
    "    $display(\"[l %m %l]\");\n"
    "    $display(\"[L %m %L]\");\n"
    "  end\n"
    "endmodule\n"
    "module m;\n"
    "  initial $display(\"[m %m %l]\");\n"
    "endmodule\n";

// The configuration under test: its design statement tops the design out in
// rtlLib, its default clause takes the RTL descriptions, and its one instance
// clause moves the second adder -- and, by inheritance, everything below it --
// to the gate-level library.
constexpr const char* kSelectingConfig =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 liblist gateLib;\n"
    "endconfig\n";

// Its companion: the same configuration with the instance clause struck out,
// which is the answer that clause displaces.
constexpr const char* kPlainConfig =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

// Writes the library map and the three source descriptions, loading the map
// before any of them so every cell is tagged through it, and parsing the RTL
// description first and the topping file last. An implementation reporting
// whichever description it parsed first would answer aLib everywhere, which
// the paired configurations below rule out. Returns false when a file does not
// parse.
bool BuildExampleDesign(ScratchDir& tmp, BoundDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, "adder.v", kAdderSource)) return false;
  if (!design.Add(tmp, "adder.vg", kAdderSource)) return false;
  return design.Add(tmp, "top.v", kTopSource);
}

// The text a run left in `path`, for the output commands that produce their
// text somewhere other than the standard output. An unwritten file reads as the
// empty string, so a test asserting on the text also rules out no file at all.
std::string FileContents(const std::filesystem::path& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}

// The instance topping the design reports the library its design statement
// named and the cell that statement named, not the name of the file or the
// name of the library the configuration itself was parsed into.
TEST(LibraryBindingDisplay, TopInstanceReportsItsDesignStatementBinding) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[t top rtlLib.top]"));
}

// A child instance the default clause bound reports that clause's library
// together with the cell name, which is the design element's name and not the
// name of the instance holding it.
TEST(LibraryBindingDisplay, ChildBoundByTheDefaultClauseReportsThatLibrary) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[l top.a1 aLib.adder]"));
}

// Its sibling, selected by the instance clause, reports the library that
// clause named -- out of a description whose text is identical to the one its
// sibling took, so the reported library came from the binding.
TEST(LibraryBindingDisplay, ChildBoundByAnInstanceClauseReportsThatLibrary) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[l top.a2 gateLib.adder]"));
}

// The companion of the claim above: with the instance clause struck out that
// very instance reports the default clause's library, so the gate-level answer
// is not where this design lands on its own.
TEST(LibraryBindingDisplay, WithoutTheClauseThatChildReportsTheDefault) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kPlainConfig, "cfg2");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[l top.a2 aLib.adder]"));
  EXPECT_FALSE(ReportsLine(out, "gateLib"));
}

// The other case of the specifier is the same specifier: written into the same
// instance, beside the lowercase form, it reports the same binding.
TEST(LibraryBindingDisplay, UppercaseSpecifierReportsTheSameBinding) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[L top.a2 gateLib.adder]"));
  EXPECT_TRUE(ReportsLine(out, "[L top.a1 aLib.adder]"));
}

// What each instance reports is its own binding, not its parent's: the cell a
// level below the adder is a different cell in a different position, and the
// two copies of it under the two adders report the two libraries their
// respective subhierarchies were bound out of.
TEST(LibraryBindingDisplay, DescendantsReportTheirOwnBinding) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[m top.a1.f1 aLib.m]"));
  EXPECT_TRUE(ReportsLine(out, "[m top.a2.f1 gateLib.m]"));
}

// With no library map read at all, a design element still belongs to a
// library -- the default one -- and the specifier reports it rather than
// leaving the library half of the token empty.
TEST(LibraryBindingDisplay, WithNoLibraryMapTheDefaultLibraryIsReported) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%l]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

// The specifier belongs to the display task's format string, and the display
// task is one textual output command among several: the write task expands it
// the same way, supplying its own newline since that family appends none.
TEST(LibraryBindingDisplay, WriteTaskExpandsTheSpecifierToo) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $write(\"[%l]\\n\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

// And the formatting function, whose textual output goes to a string rather
// than to a stream, carries the binding into that string.
TEST(LibraryBindingDisplay, FormattingFunctionCarriesTheBindingIntoAString) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = $sformatf(\"[%l]\");\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

// The two output-variable siblings of that function produce their text into a
// variable the call names rather than returning it, and expand the specifier
// on the way. The strobed and monitored commands below aside, these are the
// remaining forms in which text is formatted.
TEST(LibraryBindingDisplay, FormatIntoVariableTaskExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"[%l]\");\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, WriteIntoVariableTaskExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swrite(s, \"[%l]\");\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

// The strobed command produces its text after the time slot has settled rather
// than where it is written, so the instance it reports has to survive the
// deferral. The command is written into an instantiated cell, whose binding
// differs from the topping cell's in both halves: a deferred expansion that
// lost track of the calling instance would report the top's binding, which is
// the answer this test rules out.
TEST(LibraryBindingDisplay, StrobedCommandExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module leaf;\n"
      "  initial $strobe(\"[%l]\");\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.leaf]\n");
}

// The monitoring command is deferred the same way, and produces its text from a
// display list the run holds on to rather than from the call site, so the same
// instance question is asked of a retained list. It is written into the same
// instantiated cell for the same reason.
TEST(LibraryBindingDisplay, MonitoringCommandExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module leaf;\n"
      "  initial $monitor(\"[%l]\");\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.leaf]\n");
}

// A severity task is a textual output command too, and the binding reaches the
// message body it composes -- alongside, and distinct from, the hierarchical
// scope name that task reports of its own accord.
TEST(LibraryBindingDisplay, SeverityTaskExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $info(\"<%l>\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportsLine(out, "<work.t>"));
}

// The file-output family writes its text somewhere other than the standard
// output, and the specifier expands there just the same: the binding reaches
// the file the run opened for itself, and nothing of it reaches stdout.
TEST(LibraryBindingDisplay, FileOutputTaskExpandsTheSpecifier) {
  ScratchDir tmp;
  auto path = tmp.dir / "binding.log";
  std::string src =
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
      path.string() +
      "\", \"w\");\n"
      "    $fdisplay(fd, \"[%l]\");\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_EQ(FileContents(path), "[work.t]\n");
  EXPECT_TRUE(out.empty());
}

// A format string need not be written as a literal at the call: the formatting
// function accepts one held in a variable, and the specifier inside it is found
// and expanded when the call runs rather than when the source was read.
TEST(LibraryBindingDisplay, ARunTimeFormatStringExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string fmt;\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt = \"[%l]\";\n"
      "    s = $sformatf(fmt);\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

// A field width may be written between the percent and the letter. It is
// consumed as part of the specifier rather than left in the output as text, and
// the substitution behind it is the same binding.
TEST(LibraryBindingDisplay, AFieldWidthBeforeTheLetterIsConsumed) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%0l]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

// The specifier supplies its own substitution, so it takes no argument from
// the call the way %m takes none: a specifier that does consume one still
// reaches the single argument written after it.
TEST(LibraryBindingDisplay, SpecifierTakesNoArgumentFromTheCall) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%l][%0d]\", 8'd42);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t][42]\n");
}

// The nearest input the rule must turn away: an escaped percent leaves the
// letter as ordinary text, so a format string that never introduces a
// specifier gets no binding substituted into it.
TEST(LibraryBindingDisplay, AnEscapedPercentLeavesTheLetterLiteral) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%%l]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[%l]\n");
}

// What the specifier reports is the module instance containing the command,
// which is where it parts company with the hierarchical name: a named block
// inside that instance is part of the scope the name walk reports and no part
// of the binding, because a block is not a cell bound out of a library.
TEST(LibraryBindingDisplay, BlockScopesStayOutOfTheReportedBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial begin : blk\n"
      "    $display(\"[%m][%l]\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[t.blk][work.t]\n");
}

// A subroutine is a scope of the same kind and enters the reported binding no
// more than a block does. A task is one of the two forms it takes, and it
// contributes its own level to the hierarchical name beside an unchanged
// binding.
TEST(LibraryBindingDisplay, TaskScopeStaysOutOfTheReportedBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  task show;\n"
      "    $display(\"[%m][%l]\");\n"
      "  endtask\n"
      "  initial show;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[t.show][work.t]\n");
}

// A function is the other form, entered as an expression operand rather than as
// a statement, and it leaves the binding alone the same way.
TEST(LibraryBindingDisplay, FunctionScopeStaysOutOfTheReportedBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  function int get;\n"
      "    $display(\"[%m][%l]\");\n"
      "    return 1;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial y = get();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[t.get][work.t]\n");
}

// A generate block is elaborated into the instance holding it rather than into
// an instance of its own, so a command written inside one reports the binding
// of the module instance that contains the generate construct. The loop form is
// the one that leaves a per-iteration scope behind for the binding lookup to be
// confused by.
TEST(LibraryBindingDisplay, AGenerateBlockDoesNotPerturbTheBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 1; i = i + 1) begin : g\n"
      "      initial $display(\"[%l]\");\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

// A cell is a design element of any kind, so an instance whose bound cell is an
// interface reports its binding as a module instance does -- and reports its
// own cell rather than the cell of the module instantiating it.
TEST(LibraryBindingDisplay, AnInterfaceInstanceReportsItsOwnBinding) {
  SimFixture f;
  auto out = RunCapture(
      "interface bus;\n"
      "  initial $display(\"[%l]\");\n"
      "endinterface\n"
      "module t;\n"
      "  bus u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.bus]\n");
}

// And for a program, the other kind of design element an instantiation reaches
// by name whose body runs procedures of its own.
TEST(LibraryBindingDisplay, AProgramInstanceReportsItsOwnBinding) {
  SimFixture f;
  auto out = RunCapture(
      "program pgm;\n"
      "  initial $display(\"[%l]\");\n"
      "endprogram\n"
      "module t;\n"
      "  pgm u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.pgm]\n");
}

// Lowering records a binding for every instance it creates, so this is the one
// claim about the specifier with no source description behind it: asked for a
// binding that was never recorded, it still substitutes a library.cell-shaped
// token between the surrounding text rather than expanding to nothing.
TEST(LibraryBindingDisplay, AnUnrecordedBindingStillSubstitutesAToken) {
  SimFixture f;  // no binding registered for any instance
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("x%ly", vals, {.ctx = &f.ctx, .loc = {}});
  EXPECT_EQ(out.front(), 'x');
  EXPECT_EQ(out.back(), 'y');
  EXPECT_NE(out.find('.'), std::string::npos);
  EXPECT_GT(out.size(), 2u);
}

// The three VPI properties are three properties, each asked for by its own
// selector and none of them the selector that asks for a name.
TEST(LibraryBindingDisplay, VpiBindingPropertyConstantsAreDistinct) {
  EXPECT_NE(kVpiLibrary, kVpiCell);
  EXPECT_NE(kVpiLibrary, kVpiConfig);
  EXPECT_NE(kVpiCell, kVpiConfig);
  EXPECT_NE(kVpiLibrary, kVpiName);
  EXPECT_NE(kVpiCell, kVpiName);
  EXPECT_NE(kVpiConfig, kVpiName);
}

// A module object reports the library it was compiled into.
TEST(LibraryBindingDisplay, VpiGetStrReturnsLibraryNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->library_name = "gateLib";
  const char* lib = ctx.GetStr(kVpiLibrary, mod);
  ASSERT_NE(lib, nullptr);
  EXPECT_STREQ(lib, "gateLib");
}

// And the cell bound to the instance.
TEST(LibraryBindingDisplay, VpiGetStrReturnsCellNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->cell_name = "adder";
  const char* cell = ctx.GetStr(kVpiCell, mod);
  ASSERT_NE(cell, nullptr);
  EXPECT_STREQ(cell, "adder");
}

// Every module instance is bound to some cell, and where no cell name was
// recorded separately the cell is the design element's own -- so the property
// names it rather than answering with an empty string. The instance path is
// kept different from the cell name here, since a module whose two names
// coincide could not tell the two apart.
TEST(LibraryBindingDisplay, VpiCellFallsBackToTheModulesOwnName) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  const char* cell = ctx.GetStr(kVpiCell, mod);
  ASSERT_NE(cell, nullptr);
  EXPECT_STREQ(cell, "adder");
}

// And the configuration that controlled that binding, named the way a cell is
// named: qualified by the library holding it.
TEST(LibraryBindingDisplay, VpiGetStrReturnsConfigNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->config_name = "work.cfg5";
  const char* cfg = ctx.GetStr(kVpiConfig, mod);
  ASSERT_NE(cfg, nullptr);
  EXPECT_STREQ(cfg, "work.cfg5");
}

// They are string properties the way a name is: a module carrying neither a
// recorded library nor a recorded config still answers the string query with a
// string rather than with nothing at all. The cell has an answer of its own
// when none was recorded, which the fallback test above states.
TEST(LibraryBindingDisplay, VpiBindingPropertiesReturnStringWhenUnset) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("m", "m");
  EXPECT_NE(ctx.GetStr(kVpiLibrary, mod), nullptr);
  EXPECT_NE(ctx.GetStr(kVpiConfig, mod), nullptr);
}

// The nearest object the properties must turn away: they exist for objects of
// type vpiModule, so an object of another type -- a port of that very module
// -- answers none of them.
TEST(LibraryBindingDisplay, VpiBindingPropertiesAreModuleScoped) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("top", "top");
  VpiHandle port = ctx.CreatePort("p", kVpiInput, mod);
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, port), nullptr);
}

// And no object at all is no module either.
TEST(LibraryBindingDisplay, VpiBindingPropertiesAreNullSafe) {
  VpiContext ctx;
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, nullptr), nullptr);
}

// The route a tool actually takes to display the information: the three
// properties are reached through the public string-query entry point, under
// the selector spellings an application writes.
TEST(LibraryBindingDisplay, VpiGetStrCApiReadsBindingProperties) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiHandle mod = ctx.CreateModule("adder", "top.a1");
  mod->library_name = "rtlLib";
  mod->cell_name = "adder";
  mod->config_name = "work.cfg1";
  EXPECT_STREQ(vpi_get_str(vpiLibrary, mod), "rtlLib");
  EXPECT_STREQ(vpi_get_str(vpiCell, mod), "adder");
  EXPECT_STREQ(vpi_get_str(vpiConfig, mod), "work.cfg1");
  SetGlobalVpiContext(nullptr);
}

}  // namespace
