#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "fixture_diagnosed.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

struct SimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  Diagnosed has_errors{diag};
};

struct SimFixtureSeeded {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, 42};
  Diagnosed has_errors{diag};
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

inline std::string_view TopNameOf(const CompilationUnit* cu) {
  return cu->modules.empty() ? std::string_view() : cu->modules.back()->name;
}

template <typename Fixture>
RtlirDesign* ElaborateSrcOn(const std::string& src, Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(TopNameOf(cu));
  f.has_errors.Record(src);
  return design;
}

inline RtlirDesign* ElaborateSrc(const std::string& src, SimFixture& f) {
  return ElaborateSrcOn(src, f);
}

inline RtlirDesign* ElaborateSrcAllTops(const std::string& src, SimFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  Elaborator elab(f.arena, f.diag, parser.Parse());
  auto* design = elab.Elaborate("");
  f.has_errors.Record(src);
  return design;
}

inline RtlirDesign* ElaborateSrc(const std::string& src, SimFixtureSeeded& f) {
  return ElaborateSrcOn(src, f);
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

inline void ExpectOwnWordsCopy(const Logic4Vec& src, const Logic4Vec& dst) {
  ASSERT_NE(src.words, nullptr);
  ASSERT_NE(dst.words, nullptr);
  EXPECT_NE(src.words, dst.words);
  ASSERT_EQ(src.nwords, dst.nwords);
  for (uint32_t i = 0; i < src.nwords; ++i) {
    EXPECT_EQ(src.words[i].aval, dst.words[i].aval) << "aval word " << i;
    EXPECT_EQ(src.words[i].bval, dst.words[i].bval) << "bval word " << i;
  }
}

inline Variable* RunAndFindVar(const std::string& src, SimFixture& f,
                               std::string_view name) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindVariable(name);
}

inline std::string RunCaptureDesign(
    RtlirDesign* (*elaborate)(const std::string&, SimFixture&),
    const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = elaborate(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

inline std::string RunCapture(const std::string& src, SimFixture& f) {
  return RunCaptureDesign(ElaborateSrc, src, f);
}

inline std::string RunCaptureAllTops(const std::string& src, SimFixture& f) {
  return RunCaptureDesign(ElaborateSrcAllTops, src, f);
}

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
