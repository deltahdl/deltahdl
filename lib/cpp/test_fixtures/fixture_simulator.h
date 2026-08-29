#pragma once

#include <cstddef>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "fixture_elaborator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

struct SimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  bool has_errors = false;
};

struct SimFixtureSeeded {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

using LowerFixture = SimFixture;
using SysTaskFixture = SimFixture;
using SysTaskMathFixture = SimFixture;
using FuncFixture = SimFixture;
using ExprFixture = SimFixture;
using SyncFixture = SimFixtureSeeded;

using SampledLetFixture = SimFixture;
using CompiledSimFixture = SimFixture;
using DpiSimFixture = SimFixture;
using AssertionSimFixture = SimFixture;
using StmtFixture = SimFixtureSeeded;
using ClockingSimFixture = SimFixtureSeeded;
using MtSimFixture = SimFixture;
using SimA604Fixture = SimFixture;

inline RtlirDesign* ElaborateSrc(const std::string& src, SimFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

inline RtlirDesign* ElaborateSrc(const std::string& src, SimFixtureSeeded& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

inline Expr* ParseExprFrom(const std::string& src, SimFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

inline void LowerAndRun(const RtlirDesign* design, SimFixture& f) {
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

// Elaborates, lowers and runs `src`, then returns the context variable `name`
// the run left behind. Returns nullptr when the source does not elaborate or
// when the run declared no such variable, so a test asserts on the pointer
// before reading the value. The fixture is caller-owned, so its diagnostics
// and context stay inspectable afterwards.
inline Variable* RunAndFindVar(const std::string& src, SimFixture& f,
                               std::string_view name) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindVariable(name);
}

// Elaborates, lowers and runs `src`, returning whatever the run wrote to
// stdout. A source that does not elaborate produces no run and so no output,
// which a test reads as the empty string. The fixture is caller-owned, so its
// diagnostics stay inspectable afterwards.
inline std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// The first diagnostic at or after position `from` whose message contains
// `needle`, or nullptr when there is none. A test that asserts which rule of
// IEEE 1800-2023 a report enforces reads the subclause off this, and a null
// return says the source never provoked the report the test is about -- which
// a count of errors or warnings cannot distinguish from provoking a different
// one. A caller whose subject is a report the run raises passes the number of
// diagnostics standing before the run, so an identically worded report from an
// earlier stage is not mistaken for it.
inline const Diagnostic* FindDiagFrom(const SimFixture& f, size_t from,
                                      std::string_view needle) {
  const auto& diags = f.diag.Diagnostics();
  for (size_t i = from; i < diags.size(); ++i) {
    if (diags[i].message.find(needle) != std::string::npos) return &diags[i];
  }
  return nullptr;
}

inline const Diagnostic* FindDiag(const SimFixture& f,
                                  std::string_view needle) {
  return FindDiagFrom(f, 0, needle);
}

// The position of the first diagnostic whose message contains `needle`, or the
// number of diagnostics when none does.
//
// A test that claims a run reported exactly once, or at least twice, passes
// this position plus one to FindDiagFrom, so what it asks for is a report
// beyond the one it already named rather than a report beyond a position it
// guessed. A clause that states how many violations a construct reports is what
// makes such a claim worth writing: §31.8 has a $setup over a vector "still
// only report a single timing violation" however many bits transitioned, and
// §31.4.3's event-based $fullskew continues its window after a violation where
// the timer-based mode turns dormant.
inline std::size_t PositionOfFirstDiag(const SimFixture& f,
                                       std::string_view needle) {
  const auto& diags = f.diag.Diagnostics();
  for (std::size_t i = 0; i < diags.size(); ++i) {
    if (diags[i].message.find(needle) != std::string::npos) return i;
  }
  return diags.size();
}

inline Variable* MakeVar(SimFixture& f, std::string_view name, uint32_t width,
                         uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

inline Variable* MakeSignedVarAdv(SimFixture& f, std::string_view name,
                                  uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  var->is_signed = true;
  return var;
}
