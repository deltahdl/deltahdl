#pragma once

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "simulator/evaluation.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"

using namespace delta;

inline CompilationUnit* RunModuleSource(const std::string& src, SimFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  if (cu == nullptr || cu->modules.empty()) return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  if (design == nullptr || f.diag.HasErrors()) return nullptr;
  LowerAndRun(design, f);
  return cu;
}

inline CompilationUnit* RunSpecifyBlockSource(const std::string& specify_body,
                                              SimFixture& f) {
  return RunModuleSource(
      "module t;\n  specify\n" + specify_body + "\n  endspecify\nendmodule\n",
      f);
}

inline void RegisterPulseStyles(const ModuleDecl& mod, SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kPulsestyle) continue;
      PulseStyle style =
          si->is_ondetect ? PulseStyle::kOnDetect : PulseStyle::kOnEvent;
      for (const auto& out : si->path_outputs) {
        std::string_view sig = out.name;
        mgr.SetPathOutputPulseStyle(std::string(sig), style);
      }
    }
  }
}

inline void RegisterShowCancelled(const ModuleDecl& mod, SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kShowcancelled) continue;
      ShowCancelled mode = si->is_noshowcancelled
                               ? ShowCancelled::kNoshowcancelled
                               : ShowCancelled::kShowcancelled;
      for (const auto& out : si->path_outputs) {
        std::string_view sig = out.name;
        mgr.SetPathOutputShowCancelled(std::string(sig), mode);
      }
    }
  }
}

inline void RegisterPathPulseSpecparams(const ModuleDecl& mod, SimFixture& f,
                                        SpecifyManager& mgr) {
  std::vector<PulseControlSpecparam> specs;
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kSpecparam || !si->is_pathpulse) {
        continue;
      }
      PulseControlSpecparam s;
      s.input = si->pathpulse_input;
      s.output = si->pathpulse_output;
      s.reject = EvalExpr(si->pathpulse_reject, f.ctx, f.arena).ToUint64();
      s.has_error = si->pathpulse_error != nullptr;
      if (s.has_error) {
        s.error = EvalExpr(si->pathpulse_error, f.ctx, f.arena).ToUint64();
      }
      specs.push_back(s);
    }
  }
  mgr.ResolvePulseControlSpecparams(specs);
}

inline void RegisterTimingChecks(const ModuleDecl& mod, SimFixture& f,
                                 SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      mgr.AddTimingCheckUnderOptions(si->timing_check, f.ctx, f.arena);
    }
  }
}

inline const SpecifyPathDecl* FirstPathDeclIn(const ModuleDecl& mod) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kPathDecl) return &si->path;
    }
  }
  return nullptr;
}

inline void RegisterPathDelays(const ModuleDecl& mod, SimFixture& f,
                               SpecifyManager& mgr,
                               bool default_pulse_limits = false) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kPathDecl) continue;
      PathDelay pd = BuildPathDelayFromDecl(si->path, f.ctx, f.arena);
      if (default_pulse_limits) InitDefaultPulseLimits(pd);
      mgr.AddPathDelay(pd);
    }
  }
}

inline void RegisterSpecparamValues(const ModuleDecl& mod, SimFixture& f,
                                    SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kSpecparam || si->is_pathpulse ||
          si->param_value == nullptr) {
        continue;
      }
      SpecparamValue sp;
      sp.name = std::string(si->param_name);
      sp.value = EvalExpr(si->param_value, f.ctx, f.arena).ToUint64();
      mgr.SetSpecparamValue(std::move(sp));
    }
  }
}

inline void RegisterPrimitiveDrivers(const ModuleDecl& mod, SimFixture& f,
                                     SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kGateInst) continue;
    for (auto& driver : BuildPrimitiveDriversFromGate(*item, f.ctx, f.arena)) {
      mgr.AddPrimitiveDriver(std::move(driver));
    }
  }
}
