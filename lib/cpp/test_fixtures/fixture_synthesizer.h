#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct SynthFixture {
  SourceManager src_mgr;
  DiagEngine diag{src_mgr};
  Arena arena;
};

inline const RtlirModule* ElaborateSrc(SynthFixture& f,
                                       const std::string& src) {
  auto fid = f.src_mgr.AddFile("<test>", src);
  Lexer lexer(f.src_mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  if (!cu || cu->modules.empty()) return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  if (!design || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

// The first report whose message is exactly `message`, or null when none is.
// Matching the whole message rather than a fragment of it is what lets one
// rejection be told from another: every rejection the synthesizer writes ends
// in the words "is not synthesizable", so a search for a fragment answers with
// whichever construct the walk reached first.
inline const Diagnostic* FindDiag(const SynthFixture& f,
                                  std::string_view message) {
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.message == message) return &diag;
  }
  return nullptr;
}
