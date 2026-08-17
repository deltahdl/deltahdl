// §3.14.2.2 puts a timeunit or timeprecision declaration written outside every
// design element in the compilation-unit scope: "There shall be at most one
// time unit and one time precision for any module, program, package, or
// interface definition or in any compilation-unit scope." Every case here
// writes such a declaration into a file compiled through SinglePassCompiler and
// reads the value back off the elaborated design, which is the pair of objects
// no other test in this tier spans: the parser writes the declaration onto the
// CompilationUnit it built for one file, and what the elaborator reads is the
// merged unit AppendCompilationUnitDeclarations in src/parser/ast_design.h
// assembled out of the command line.
//
// The cases from ConflictingCompilationUnitTimeunitsAcrossFilesAreReported
// onwards write a declaration into each of two files of one command line and
// read a report back rather than a value, because §3.12.1 case a) puts those
// two declarations in one time scope and §3.14.2.2 requires the second to match
// the first.
//
// Every case declares picoseconds, which is what tells a declaration that
// reached the design from one that did not. `cu_time_unit` and `cu_time_prec`
// are both initialized to TimeUnit::kNs and both magnitudes to 1 in `struct
// CompilationUnit` at src/parser/ast_design.h, and TimeScale in
// src/common/types.h has the same four defaults, so a case declaring `timeunit
// 1ns;` reports the right answer whether the declaration was carried or
// dropped. The cases that read a magnitude back declare one other than 1 for
// the same reason. §3.14.2.2 admits the magnitude: its own example writes
// `timeunit 100ps;`.

#include <gtest/gtest.h>

#include <filesystem>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

// The infrastructure one command line is compiled and elaborated against.
struct CommandLineHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

// The library map every test here compiles against. A compilation-unit
// declaration belongs to no library, so the map claims the sources only so that
// the design elements among them have somewhere to go.
constexpr const char* kLibMap = "library rtlLib src/*.sv;\n";

// Compiles `files` as one command line into `h` and elaborates the compilation
// unit that produced, returning the design or nullptr. The design outlives the
// elaborator because it is arena-allocated, and the arena is the harness's.
RtlirDesign* CompileCommandLineAndElaborate(CommandLineHarness& h,
                                            const ScratchDir& tmp,
                                            const std::vector<fs::path>& files,
                                            std::string_view top) {
  if (!h.libs.LoadMapFile(tmp.dir / "lib.map")) return nullptr;
  if (!h.compiler.CompileCommandLine(files, h.unit)) return nullptr;
  Elaborator elab(h.arena, h.diag, &h.unit);
  return elab.Elaborate(top);
}

// The module of a design that came out as exactly one top module, or nullptr.
// The fallback case reads its resolved time unit through this.
const RtlirModule* SoleTopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return nullptr;
  return design->top_modules[0];
}

TEST(SinglePassCompileTimescale, ACompilationUnitTimeunitReachesTheDesign) {
  // One file whose first item is `timeunit 100ps;`, written outside the module
  // that follows it. §3.14.2.2 gives that declaration to the compilation-unit
  // scope -- "There shall be at most one time unit and one time precision for
  // any module, program, package, or interface definition or in any
  // compilation-unit scope" -- and requires the position: "If specified, the
  // timeunit and timeprecision declarations shall precede any other items in
  // the current time scope."
  //
  // The reader is src/elaborator/elaborator.cpp, which sets
  // design->cu_timescale.unit and .magnitude only under unit->has_cu_timeunit.
  // That flag is set on the CompilationUnit the parser built for this file, so
  // the design reports 1 ns unless the merge carries it onto the unit the
  // elaborator was handed. §20.4.1 makes design->cu_timescale what
  // $timeunit/$timeprecision report for the $unit argument.
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto src = tmp.Write("src/top.sv",
                       "timeunit 100ps;\n"
                       "module top;\n"
                       "endmodule\n");

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(h, tmp, {src}, "");
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->cu_timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(design->cu_timescale.magnitude, 100);
}

TEST(SinglePassCompileTimescale,
     ACompilationUnitTimeprecisionReachesTheDesign) {
  // The precision half on its own, in the second form §3.14.2.2 gives it: "The
  // time unit and precision can be declared by the timeunit and timeprecision
  // keywords, respectively, and set to a time literal." The declaration stands
  // outside the module, so it is the compilation unit's precision and not that
  // module's.
  //
  // This is a separate case from the time unit rather than the same one twice.
  // src/elaborator/elaborator.cpp gates design->cu_timescale.precision and
  // .prec_magnitude on unit->has_cu_timeprecision, which is a different flag
  // from unit->has_cu_timeunit and set by a different arm of ApplyCuTimeUnit in
  // src/parser/parser_timeunit.cpp, so a merge carrying one half would pass a
  // case asserting only the other.
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto src = tmp.Write("src/top.sv",
                       "timeprecision 10ps;\n"
                       "module top;\n"
                       "endmodule\n");

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(h, tmp, {src}, "");
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->cu_timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(design->cu_timescale.prec_magnitude, 10);
}

TEST(SinglePassCompileTimescale,
     ATimeunitInOneFileSetsTheFallbackForAModuleInAnother) {
  // Two files on one command line: the first declares `timeunit 100ps;` and no
  // design element at all, the second declares a module that declares no time
  // unit of its own. §3.12.1 case a) makes the two files one compilation unit
  // -- "all files on a given compilation command line make a single compilation
  // unit" -- so the declaration in the first is the second's compilation-unit
  // scope, and §3.14.2.3 case c) then decides the module's time unit: "Else, if
  // the compilation-unit scope specifies a time unit (outside all other
  // declarations), then the time unit shall be set to the time units of the
  // compilation unit."
  //
  // The reader is src/elaborator/elaborator_module.cpp, which falls back to
  // unit->cu_time_unit and unit->cu_time_unit_magnitude for a design element
  // whose own decl->has_timeunit is false. That fallback is reached here and is
  // not reached by the two cases above, which read design->cu_timescale
  // instead, and the value it produces is what every delay in the module is
  // scaled by.
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto cu = tmp.Write("src/cu.sv", "timeunit 100ps;\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {cu, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.magnitude, 100);
}

TEST(SinglePassCompileTimescale,
     ACompilationUnitPrecisionEntersTheGlobalPrecisionSearch) {
  // A command line whose only declared precision anywhere is the compilation
  // unit's: the first file declares `timeprecision 10ps;` outside every design
  // element, the second declares a module that declares neither a time unit nor
  // a precision. §3.14.3 makes that declaration the tick size of the whole run:
  // "The global time precision, also called the simulation time unit, is the
  // minimum of all the timeprecision statements, all the time precision
  // arguments to timeunit declarations, and the smallest time precision
  // argument of all the `timescale compiler directives in the design."
  //
  // The reader is ComputeGlobalTimePrecision in src/parser/time_resolve.cpp,
  // which offers cu->cu_time_prec to the minimum only under
  // cu->has_cu_timeprecision, reached from src/elaborator/elaborator.cpp. It is
  // a third reader of the same two members, separate from the §20.4.1 one the
  // precision case above covers: a design that reports the right $unit
  // precision and still runs on nanosecond ticks is wrong by a factor of a
  // hundred in every delay it schedules.
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto cu = tmp.Write("src/cu.sv", "timeprecision 10ps;\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "endmodule\n");

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(h, tmp, {cu, top}, "");
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->global_time_precision, TimeUnit::kPs);
}

// The cases below put a compilation-unit declaration in each of two files of
// one command line. §3.12.1 case a) makes the two one compilation unit -- "All
// files on a given compilation command line make a single compilation unit (in
// which case the declarations within those files are accessible following
// normal visibility rules throughout the entire set of files)" -- so the two
// declarations stand in one time scope, and §3.14.2.2 rules on the pair: "The
// timeunit and timeprecision declarations can be repeated as later items, but
// shall match the previous declaration within the current time scope."
//
// The declaration in src/first.sv stands on line 1 of that file and the one in
// src/second.sv on line 2 of its own, so the line a report stands at says which
// of the two declarations it names. Two declarations on one line number are
// what a case cannot tell apart, and the standard leaves room for the second
// file to open with something: §3.14.2.2 requires only that "the timeunit and
// timeprecision declarations shall precede any other items in the current time
// scope", and a comment is no item.

// The declaration src/first.sv carries, one per case: the time unit for three
// of them and the time precision for the one that is about the precision. The
// file holds no design element, so nothing but the declaration crosses to the
// other file.
constexpr const char* kFirstFileTimeunitPs = "timeunit 1ps;\n";
constexpr const char* kFirstFileTimeprecisionPs = "timeprecision 1ps;\n";

// Writes src/first.sv, src/second.sv and the library map into `tmp`, and
// answers the command line naming the two sources in that order.
std::vector<fs::path> TwoFileCommandLine(ScratchDir& tmp, const char* first,
                                         const char* second) {
  tmp.Write("lib.map", kLibMap);
  return {tmp.Write("src/first.sv", first), tmp.Write("src/second.sv", second)};
}

// Compiles `files` as one command line into `h` and elaborates nothing,
// answering nothing about whether the command line compiled. A case reading a
// report back through ReportedError is not answered by the outcome: whether a
// report about the second file's declaration leaves that file failed turns on
// where in SinglePassCompiler::CompileSource the report stands, and §3.14.2.2
// rules that the report is made rather than what it costs the compile.
void CompileTwoFileCommandLine(CommandLineHarness& h, const ScratchDir& tmp,
                               const std::vector<fs::path>& files) {
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  h.compiler.CompileCommandLine(files, h.unit);
}

TEST(SinglePassCompileTimescale,
     ConflictingCompilationUnitTimeunitsAcrossFilesAreReported) {
  // `timeunit 1ps;` in one file of a command line and `timeunit 1ns;` in
  // another, which §3.14.2.2 forbids: the repeat "shall match the previous
  // declaration within the current time scope", and §3.12.1 case a) is what
  // makes the two files one time scope. What the source description costs is a
  // run at the wrong tick size with nothing said, since §3.14.2.3 case c) makes
  // the compilation unit's time unit the fallback for every design element
  // declaring none of its own and the two readings are a factor of a thousand
  // apart.
  //
  // CheckCuTimeunitConsistency in src/parser/parser.cpp already makes this
  // exact report within one file, so the message and the subclause are the ones
  // it uses rather than a second wording for one rule. The line is the second
  // declaration's, which is the one the source description has to change to
  // conform, and it is line 2 of src/second.sv where the first declaration
  // stands on line 1 of src/first.sv.
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The later of the two declarations follows this line.\n"
      "timeunit 1ns;\n"
      "module top;\n"
      "endmodule\n";

  CommandLineHarness h;
  CompileTwoFileCommandLine(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeunitPs, kSecondFile));
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(), "timeunit does not match prior declaration",
      LineHolding(kSecondFile, "timeunit 1ns;"), "3.14.2.2"));
}

TEST(SinglePassCompileTimescale,
     ConflictingCompilationUnitTimeprecisionsAcrossFilesAreReported) {
  // The precision half of the same rule, which §3.14.2.2 states of both at
  // once: "There shall be at most one time unit and one time precision for any
  // module, program, package, or interface definition or in any
  // compilation-unit scope."
  //
  // This is a separate case from the time unit rather than the same one twice.
  // CheckCuTimeunitConsistency in src/parser/parser.cpp reaches the two through
  // different branches, reading cu_time_prec and cu_time_prec_magnitude under
  // has_cu_timeprecision where the unit half reads cu_time_unit and
  // cu_time_unit_magnitude under has_cu_timeunit, so a comparison written
  // across files for one of them would leave a case asserting only the other
  // green.
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The later of the two precision declarations follows this line.\n"
      "timeprecision 1ns;\n"
      "module top;\n"
      "endmodule\n";

  CommandLineHarness h;
  CompileTwoFileCommandLine(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeprecisionPs, kSecondFile));
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(), "timeprecision does not match prior declaration",
      LineHolding(kSecondFile, "timeprecision 1ns;"), "3.14.2.2"));
}

TEST(SinglePassCompileTimescale,
     AMatchingCompilationUnitTimeunitInASecondFileIsAccepted) {
  // Both files declare `timeunit 1ps;`, which §3.14.2.2 permits: "The timeunit
  // and timeprecision declarations can be repeated as later items, but shall
  // match the previous declaration within the current time scope." A repeat
  // that matches is a conforming source description, so a comparison across
  // files that reported every second declaration rather than every differing
  // one fails here while passing the two cases above.
  //
  // The assertion is over every diagnostic the run recorded rather than over
  // DiagEngine::HasErrors(), because a report about a declaration the standard
  // permits is wrong whichever severity it carries.
  //
  // Both files declare picoseconds and not nanoseconds. `cu_time_unit` is
  // initialized to TimeUnit::kNs in `struct CompilationUnit` at
  // src/parser/ast_design.h, so a case declaring nanoseconds reads back the
  // same value whether the declaration crossed to the elaborated design or was
  // dropped on the way, and could not fail.
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The repeat of the first file's declaration follows this line.\n"
      "timeunit 1ps;\n"
      "module top;\n"
      "endmodule\n";

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeunitPs, kSecondFile), "");
  EXPECT_TRUE(h.diag.Diagnostics().empty());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->cu_timescale.unit, TimeUnit::kPs);
}

TEST(SinglePassCompileTimescale, ConflictingMagnitudesInOneUnitAreReported) {
  // `timeunit 1ps;` against `timeunit 10ps;`, which name one time unit and
  // differ only in the magnitude. §3.14.2.2 requires the repeat to "match the
  // previous declaration", and a declaration is the time literal §5.8 admits
  // rather than the unit alone, so these two do not match and the second is
  // reported.
  //
  // The pair is what separates a comparison of cu_time_unit from a comparison
  // of the declaration. Both files leave cu_time_unit at TimeUnit::kPs and only
  // cu_time_unit_magnitude differs, so a comparison of the unit alone passes
  // both conflict cases above and fails only here. What it costs is the same
  // factor a comparison catching it would have caught: §3.14.2.3 case c) hands
  // the compilation unit's time unit to every design element declaring none,
  // and ten picoseconds is not one.
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The declaration that differs in magnitude follows this line.\n"
      "timeunit 10ps;\n"
      "module top;\n"
      "endmodule\n";

  CommandLineHarness h;
  CompileTwoFileCommandLine(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeunitPs, kSecondFile));
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(), "timeunit does not match prior declaration",
      LineHolding(kSecondFile, "timeunit 10ps;"), "3.14.2.2"));
}
