#pragma once

#include "fixture_elaborator.h"

#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

struct SimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
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
using SvaFixture = SimFixture;
using SampledLetFixture = SimFixture;
using CompiledSimFixture = SimFixture;
using DpiSimFixture = SimFixture;
using AssertionSimFixture = SimFixture;
using RealFixture = SimFixture;

using StmtFixture = SimFixtureSeeded;
using ClockingSimFixture = SimFixtureSeeded;

inline RtlirDesign* ElaborateSrc(const std::string& src, SimFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

inline RtlirDesign* ElaborateSrc(const std::string& src,
                                 SimFixtureSeeded& f) {
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

inline Variable* MakeVar(SimFixture& f, std::string_view name,
                         uint32_t width, uint64_t val) {
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
