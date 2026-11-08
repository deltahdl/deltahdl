#pragma once

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

struct BoundDesign : LibraryDesign {
  Scheduler scheduler{arena};
  SimContext ctx{scheduler, arena, diag};
};

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

inline bool ReportsLine(const std::string& out, const std::string& line) {
  return out.find(line) != std::string::npos;
}
