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
  Lexer lexer(f.mgr.FileContent(fid2), fid2, f.diag);
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
