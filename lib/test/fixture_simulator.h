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
using SyncFixture = SimFixture;
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
