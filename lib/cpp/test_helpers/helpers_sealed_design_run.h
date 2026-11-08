#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "helpers_bound_from_library.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

inline void RunUnderKey(const std::string& source, std::string_view key,
                        SimFixture& f) {
  PreprocConfig config;
  config.protect_key = std::string(key);
  Preprocessor pp(f.mgr, f.diag, config);
  std::string text = pp.Preprocess(f.mgr.AddFile("<test>", source));
  uint32_t fid = f.mgr.AddPreprocessedFile("<test>", text, pp.LineOrigins());
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  Elaborator elab(f.arena, f.diag, parser.Parse());
  RtlirDesign* design = elab.Elaborate("t");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
}

inline void RunBoundFromALibrary(const std::string& source,
                                 std::string_view key, SimFixture& f) {
  ScratchDir tmp;
  SeparateCompilationBinder binder(f.mgr, f.arena, f.diag);
  RtlirDesign* design = BoundFromALibrary(tmp, {source}, key, binder);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
}
