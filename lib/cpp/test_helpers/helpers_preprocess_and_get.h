#pragma once

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "preprocessor/preprocessor.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// Selects which preprocessor state (if any) is propagated onto the
// CompilationUnit before elaboration.
enum class CuPropagation { kNone, kDefaultNetType, kUnconnectedDrive };

// Runs the full preprocess -> parse -> elaborate -> lower -> simulate pipeline
// on an already-registered source file and returns the resulting value of
// `var_name`. The source `fid` is preprocessed, then parsed and simulated.
inline uint64_t RunPreprocessedSim(SimFixture& f, uint32_t fid,
                                   const char* var_name, Preprocessor& pp,
                                   CuPropagation prop = CuPropagation::kNone) {
  auto preprocessed = pp.Preprocess(fid);
  auto fid2 = f.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f.mgr.FileContent(fid2), fid2, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  if (prop == CuPropagation::kDefaultNetType) {
    cu->default_nettype = pp.DefaultNetType();
  } else if (prop == CuPropagation::kUnconnectedDrive) {
    cu->unconnected_drive = pp.UnconnectedDrive();
  }
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// Convenience overload that builds a fresh SimFixture, registers `src` as the
// top-level source, and simulates it.
inline uint64_t PreprocessAndGet(const std::string& src, const char* var_name,
                                 CuPropagation prop = CuPropagation::kNone) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  return RunPreprocessedSim(f, fid, var_name, pp, prop);
}

// The same, for a §22.14 test: `body` is wrapped in a real `begin_keywords
// region for `spec` and driven through the whole pipeline, and the value of
// `var_name` at the end of the run is returned. Checking the diagnostics is
// what keeps the result meaningful -- source the specifier's list admits has
// to run clean, not merely produce a number after the front end recovered
// from something it rejected -- and the unterminated-region report is asked
// for because a region the directive left open is one of the things that
// would make it dirty.
inline uint64_t RunUnderKeywordVersion(const char* spec,
                                       const std::string& body,
                                       const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>", std::string("`begin_keywords \"") + spec +
                                         "\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}
