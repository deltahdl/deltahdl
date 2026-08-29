// Whether a run registers the timing checks a design declares.
//
// Each case elaborates a source, lowers it, runs it, and then asks
// SpecifyManager -- the one the run installed on SimContext, reached through
// SimContext::GetSpecifyManager -- what it holds. No case builds a
// TimingCheckEntry of its own or calls
// SpecifyManager::AddTimingCheckUnderOptions, which is what separates this file
// from every other §31 simulator file in the tree: those construct the entry
// the case then reads, or call the fixture helper RegisterTimingChecks in
// lib/cpp/test_fixtures/fixture_specify_manager.h, so they pass whether or not
// anything under src/ ever registers a check.
//
// Issue #3403 is that nothing did. RegisterSpecifyBlocks in
// src/simulator/specify_register.cpp registered the specparam declarations, the
// module path delays, the pulsestyle and showcancelled declarations and the
// PATHPULSE$ specparams of Syntax 30-1, and none of its system timing checks,
// so SpecifyManager::GetTimingChecks answered empty in every run of every
// design. §31.2 puts a system timing check inside a specify block and §30.3
// puts that block inside a module declaration, exactly as it puts a module path
// declaration there, so a declared check belongs to one module instance the way
// a declared path does.
//
// A registered check is not yet evaluated against a stimulus. Nothing under
// src/ watches a reference or data signal and calls
// SpecifyManager::CheckSetupViolation or any of its siblings; every caller of
// those is a unit test. So no case here drives a design and expects a violation
// report, and none asserts that one was produced. What these cases assert is
// what the manager holds after the run.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, and so that none of them is the 0 that TimingCheckEntry::limit holds
// before a limit expression has been evaluated into it. The three limits are 7,
// 19 and 29, all distinct: a limit answered out of the wrong design or out of
// an unevaluated entry reads as another of the three or as 0, never as the
// right one. The two instances of one cell are told apart by
// TimingCheckEntry::inst_prefix and not by their limits, both cells being the
// same cell, so they share 19 the way two instances share a declaration.
//
// No module here is named `cell`. §33.4 gives `cell` to a config declaration's
// cell clause, so Parser rejects it as a module name; the cells below carry a
// suffix for that reason.
//
// Each source puts the cell first and the top last, because ElaborateSrc in
// lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// §30.4.1's terminal direction rules govern a module path's source and
// destination and not a timing check's signals: CheckSpecifyItemTerminals in
// src/elaborator/elaborator_validate_specify.cpp applies CheckPathDeclTerminals
// to a path declaration and applies CheckTimingTerminal to a timing check, and
// CheckTimingTerminal enforces one rule only -- §25.6's ban on a `ref` port, or
// on a signal reached through a `ref` modport member, standing as a specify
// terminal. The one further rule a source here has to satisfy is §31.2's on the
// limit, which ValidateTimingCheckLimitOperands enforces: every operand of a
// timing_check_limit is a literal or a specparam in scope.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

// The SpecifyManager `source` leaves on `f.ctx` once it has been elaborated,
// lowered and run. Null when the source did not elaborate cleanly, so a case
// asserts on the pointer before reading anything through it.
const SpecifyManager* SpecifyStateAfterRun(const std::string& source,
                                           SimFixture& f) {
  auto* design = ElaborateSrc(source, f);
  if (design == nullptr || f.has_errors) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.GetSpecifyManager();
}

// The first registered timing check of kind `kind`. Used by the case whose
// subject is that any check was registered at all, which has no instance to
// name before it has read one.
const TimingCheckEntry* RegisteredCheckOfKind(const SpecifyManager& mgr,
                                              TimingCheckKind kind) {
  for (const auto& check : mgr.GetTimingChecks()) {
    if (check.kind == kind) return &check;
  }
  return nullptr;
}

// The registered timing check the instance whose hierarchical prefix is
// `prefix` declared. Two instances of one cell declare checks naming identical
// signals, so the prefix is the only thing that separates them.
const TimingCheckEntry* RegisteredCheckIn(const SpecifyManager& mgr,
                                          std::string_view prefix) {
  for (const auto& check : mgr.GetTimingChecks()) {
    if (check.inst_prefix == prefix) return &check;
  }
  return nullptr;
}

// §31.2: a $setup declared in a specify block reaches the run. The entry is
// read back whole -- its kind, its reference signal and edge, its data signal
// and its limit -- because a registration that dropped any one of them would
// leave the check unevaluatable while still answering that something was
// registered. §31.3.1 orders the arguments data_event, reference_event,
// timing_check_limit, so `d` is the data event and `clk` the reference.
TEST(RegisteredDesignTimingChecks, DeclaredSetupCheckReachesTheManager) {
  SimFixture f;
  const SpecifyManager* mgr = SpecifyStateAfterRun(
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 7);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const TimingCheckEntry* check =
      RegisteredCheckOfKind(*mgr, TimingCheckKind::kSetup);
  ASSERT_NE(check, nullptr);
  // Syntax 31-3 writes `$setup(data_event, reference_event, limit)` where
  // Syntax 31-4 writes `$hold(reference_event, data_event, limit)`, so the two
  // clauses order their events oppositely. Parser::ParseTimingCheck reads the
  // terminals positionally and swaps them for $setup alone, which is why `clk`
  // is the reference here and `d` the data.
  EXPECT_EQ(check->ref_signal, "clk");
  EXPECT_EQ(check->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(check->data_signal, "d");
  EXPECT_EQ(check->limit, 7u);
}

// §30.3: the specify block holding a timing check stands in a module
// declaration, so each instance of a cell declares its own check and a cell
// instantiated twice registers two. §31.2 has the check name its signals by the
// bare names of the module it stands in, so both entries carry the same
// ref_signal and data_signal; inst_prefix is what tells them apart, and a
// registration that recorded only the declaration would hold one entry rather
// than two.
TEST(RegisteredDesignTimingChecks,
     TwoInstancesOfOneCellRegisterTheirOwnChecks) {
  SimFixture f;
  const SpecifyManager* mgr = SpecifyStateAfterRun(
      "module setup_cell(input d, input clk, output q);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 19);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic first_q;\n"
      "  logic second_q;\n"
      "  setup_cell u_first(1'b0, 1'b0, first_q);\n"
      "  setup_cell u_second(1'b0, 1'b0, second_q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->TimingCheckCount(), 2u);
  const TimingCheckEntry* first = RegisteredCheckIn(*mgr, "u_first.");
  ASSERT_NE(first, nullptr);
  EXPECT_FALSE(first->data_signal.empty());
  const TimingCheckEntry* second = RegisteredCheckIn(*mgr, "u_second.");
  ASSERT_NE(second, nullptr);
  EXPECT_FALSE(second->data_signal.empty());
}

// §31.2: "timing check limit values are constant expressions that can include
// specparams". The specparam is declared inside the specify block, which is
// where Syntax 30-1 puts a specparam_declaration beside the system_timing_check
// that reads it, and which RegisterSpecparams binds under the instance prefix
// before any other pass of RegisterSpecifyBlocks runs. §6.20.5 admits the
// module body as a second site, and RegisterModuleSpecparams binds that one,
// but it is bound after RegisterSpecifyBlocks has returned; the in-block site
// is the one whose binding is settled by the time a limit in the same block is
// evaluated.
//
// The limit is read back at 29, the value the cell declared. A limit evaluated
// under the wrong instance prefix finds no variable of that name and folds to
// 0, so the entry answering 29 says the specparam was read in the instance that
// declared it.
TEST(RegisteredDesignTimingChecks, SpecparamLimitIsReadInDeclaringInstance) {
  SimFixture f;
  const SpecifyManager* mgr = SpecifyStateAfterRun(
      "module limited_cell(input d, input clk, output q);\n"
      "  specify\n"
      "    specparam T = 29;\n"
      "    $setup(d, posedge clk, T);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic only_q;\n"
      "  limited_cell u_only(1'b0, 1'b0, only_q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const TimingCheckEntry* check = RegisteredCheckIn(*mgr, "u_only.");
  ASSERT_NE(check, nullptr);
  EXPECT_EQ(check->limit, 29u);
}

}  // namespace
