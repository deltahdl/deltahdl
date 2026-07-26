#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulator/evaluation.h"
#include "simulator/specify.h"

using namespace delta;

// The SystemVerilog side of a specify-block test, built from real source
// rather than hand-assembled. A module is parsed, elaborated, lowered and run,
// and the specify items it declared are registered onto a SpecifyManager
// through the production builders -- which is what makes the manager's
// contents a consequence of the syntax the subclause is about.
//
// The specify runtime is not wired into RTLIR, so registration is a step of
// its own. It is one call per specify item kind, because what an item means
// differs by subclause: a test registers the kinds the rule it covers is
// about and leaves the manager empty of everything else.

// Parses, elaborates, lowers and runs `src`, returning the compilation unit so
// a caller can walk the declarations it holds. Returns nullptr when the source
// declares no module, or when elaboration fails or reports a diagnostic. The
// fixture is caller-owned, so the arena holding the declarations outlives the
// call and the context keeps whatever the run left in it.
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

// The same for a module whose whole content is one specify block, which is
// what a test about a specify item alone needs.
inline CompilationUnit* RunSpecifyBlockSource(const std::string& specify_body,
                                              SimFixture& f) {
  return RunModuleSource(
      "module t;\n  specify\n" + specify_body + "\n  endspecify\nendmodule\n",
      f);
}

// The pulsestyle_onevent and pulsestyle_ondetect declarations of Syntax 30-8,
// each selecting the style for every path output it names.
inline void RegisterPulseStyles(const ModuleDecl& mod, SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kPulsestyle) continue;
      PulseStyle style =
          si->is_ondetect ? PulseStyle::kOnDetect : PulseStyle::kOnEvent;
      for (std::string_view sig : si->signal_list) {
        mgr.SetPathOutputPulseStyle(std::string(sig), style);
      }
    }
  }
}

// The showcancelled and noshowcancelled declarations of Syntax 30-9, each
// selecting the mode for every path output it names.
inline void RegisterShowCancelled(const ModuleDecl& mod, SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kShowcancelled) continue;
      ShowCancelled mode = si->is_noshowcancelled
                               ? ShowCancelled::kNoshowcancelled
                               : ShowCancelled::kShowcancelled;
      for (std::string_view sig : si->signal_list) {
        mgr.SetPathOutputShowCancelled(std::string(sig), mode);
      }
    }
  }
}

// The PATHPULSE$ specparams of §30.7.1, collected across the module and then
// resolved onto the manager in one call. Resolving is what applies them, and
// it happens after the whole set is known because a more specific PATHPULSE$
// overrides a less specific one, so a caller registers the path delays these
// limit before calling this.
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
      specs.push_back(std::move(s));
    }
  }
  mgr.ResolvePulseControlSpecparams(specs);
}

// The timing check declarations of §31.2, registered through the builder that
// applies the invocation options in force.
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

// The first module path declaration `mod` holds, or nullptr when it declares
// none. A test whose subject is one path's delay names it this way rather
// than walking the module itself.
inline const SpecifyPathDecl* FirstPathDeclIn(const ModuleDecl& mod) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kPathDecl) return &si->path;
    }
  }
  return nullptr;
}

// The module path assignments of §30.4, each built into a PathDelay by the
// production builder. `default_pulse_limits` starts the path's pulse limits
// out equal to its delay, which is the §30.7 default and the prebackannotation
// state a PATHPULSE$ specparam or an SDF pulse limit replaces; a test whose
// subject is the delay alone leaves it off.
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

// The §6.20.5 specparam declarations that carry an ordinary named value, which
// is every specparam but PATHPULSE$ -- that one names a pulse limit rather
// than a timing value, and RegisterPathPulseSpecparams carries it.
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

// The gate instantiations that drive a module output, which is where a
// primitive's own delay lives -- an SDF construct may annotate one, so a test
// about that needs the drivers the gates produce.
inline void RegisterPrimitiveDrivers(const ModuleDecl& mod, SimFixture& f,
                                     SpecifyManager& mgr) {
  for (auto* item : mod.items) {
    if (item->kind != ModuleItemKind::kGateInst) continue;
    for (auto& driver : BuildPrimitiveDriversFromGate(*item, f.ctx, f.arena)) {
      mgr.AddPrimitiveDriver(std::move(driver));
    }
  }
}
