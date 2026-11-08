#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

enum class CuPropagation : std::uint8_t {
  kNone,
  kDefaultNetType,
  kUnconnectedDrive
};

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

inline uint64_t PreprocessAndGet(const std::string& src, const char* var_name,
                                 CuPropagation prop = CuPropagation::kNone) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  return RunPreprocessedSim(f, fid, var_name, pp, prop);
}

inline std::string PreprocessAndCapture(const std::string& src, SimFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  auto preprocessed = pp.Preprocess(fid);
  auto fid2 = f.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f.mgr.FileContent(fid2), fid2, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  ApplyModuleDirectives(cu, pp.ModuleDirectivesList());
  cu->has_preproc_global_precision = pp.HasGlobalPrecision();
  cu->preproc_global_precision = pp.GlobalPrecision();
  cu->preproc_global_precision_magnitude = pp.GlobalPrecisionMagnitude();
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  if (design != nullptr) {
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    f.scheduler.Run();
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

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
