#pragma once

#include <iostream>
#include <sstream>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

// A mapped multi-file design assembled from source files, carrying the
// simulator state a run of it needs.
//
// §33.2 has a configuration name the source description that represents each
// instance, so what a configuration bound is read by running the design rather
// than by inspecting it, and the scheduler and the context the lowered
// hierarchy runs in travel with the unit they were built from.
struct BoundDesign : LibraryDesign {
  Scheduler scheduler{arena};
  SimContext ctx{scheduler, arena, diag};
};

// Parses `config_text` into `design`, elaborates the configuration `name`
// names, lowers the bound hierarchy into the design's simulator context and
// runs it, returning whatever the run wrote to stdout. An empty string comes
// back where the configuration was not parsed, was not found, or did not
// elaborate, so a caller asserting on the text also rules out a run that never
// happened.
//
// The search order the loaded map yields is installed before elaboration,
// which is what leaves the configuration's clauses something to override: a
// test could otherwise not tell a clause being obeyed from a map order that
// happened to agree with it.
inline std::string RunConfiguredDesign(ScratchDir& tmp, BoundDesign& design,
                                       const std::string& config_text,
                                       std::string_view name) {
  if (!design.Add(tmp, "cfg.sv", config_text)) return "";
  const auto* cfg = design.ConfigNamed(name);
  if (cfg == nullptr) return "";
  Elaborator elab(design.arena, design.diag, design.unit);
  elab.SetLibraryDeclarationOrder(design.map.ResolveSearchOrder({}));
  auto* elaborated = elab.Elaborate(cfg);
  if (elaborated == nullptr) return "";
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  Lowerer lowerer(design.ctx, design.arena, design.diag);
  lowerer.Lower(elaborated);
  design.scheduler.Run();
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Whether `line` appears somewhere in `out`. Instances of one design report at
// the same simulation time and in no order clause 33 fixes, so a claim about
// one of them is read as the presence of its own line rather than as the whole
// transcript.
inline bool ReportsLine(const std::string& out, const std::string& line) {
  return out.find(line) != std::string::npos;
}
