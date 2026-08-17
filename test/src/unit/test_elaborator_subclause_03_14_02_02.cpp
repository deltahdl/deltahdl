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
// Every case declares picoseconds, and a magnitude other than 1. `cu_time_unit`
// and `cu_time_prec` are both initialized to TimeUnit::kNs and both magnitudes
// to 1 in `struct CompilationUnit` at src/parser/ast_design.h, and TimeScale in
// src/common/types.h has the same four defaults, so a case declaring `timeunit
// 1ns;` reports the right answer whether the declaration was carried or
// dropped. §3.14.2.2 admits the magnitude: its own example writes `timeunit
// 100ps;`.

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
