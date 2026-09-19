#include <gtest/gtest.h>

#include "fixture_simulator.h"

// §16.4.3 "Deferred assertions outside procedural code".
//
// A deferred immediate assertion written outside any procedure (as a module
// item) is a "static deferred assertion" and is treated as if it were the sole
// statement of an always_comb procedure. The elaborator carries this rule by
// synthesizing an implicit always_comb process around the assertion
// (elaborator_items_assertions.cpp, IsStaticDeferredAssertion), so at run time
// the assertion inherits always_comb behaviour: it is evaluated once after the
// initial settling and re-evaluated whenever one of the boolean's combinational
// operands changes -- the semantics supplied by the always_comb dependency
// (§9.2.2.2).
//
// These tests observe that end-to-end. There is NO explicit always_comb or
// initial wrapping the assertion in the source; the only reason it executes at
// all is the §16.4.3 wrapping. The input is built from real module-level source
// and driven through parse/elaborate/lower/run, so the live simulator applies
// the rule rather than a hand-built process.

using namespace delta;

namespace {

// Both fail actions below are a single subroutine call, because §16.4 says "the
// pass and fail statements in a deferred assertion's action_block, if present,
// shall each consist of a single subroutine call" -- an assignment is not one.
// Each calls a void function that counts the firing, which is legal for an
// observed (#0) deferred assertion because §16.4 schedules that call in the
// Reactive region.

// The static deferred assertion runs even though the source contains no
// procedure: when its boolean is false the failure's else action executes,
// which is only possible because §16.4.3 turned the module-item assertion into
// an implicit always_comb process. a and b differ from their initializers, so
// the deferred assert fails and its else action records the firing; observing
// fires==1 shows the assertion executed with no procedure written.
TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertExecutesWithoutProcedure) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b1;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// The static deferred assertion inherits always_comb sensitivity: it is not a
// one-shot at time zero but re-evaluates when a combinational operand changes.
// At time zero a==b, so the assertion passes and does not fire. When the
// initial block later drives b to a different value, the implicit always_comb
// re-runs, the boolean is now false, and the else action fires. Observing
// fires==1 (not 0) shows the module-item assertion re-triggered on the operand
// change -- exactly the always_comb treatment §16.4.3 mandates.
TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertReevaluatesOnOperandChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b0;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "  initial #1 b = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// Treated as an always_comb, the static deferred assertion reaches §16.4.2's
// flush point when an operand changes again in the same time step: the
// evaluation that saw a at 7 against b at 5 queued its else action, the
// re-run for b's write from the Inactive region flushed it, and the re-run
// found the two equal, so nothing fires.
TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertIsFlushedByASecondOperandChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a = 4'd5;\n"
      "  logic [3:0] b = 4'd5;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "  initial begin\n"
      "    #1 a = 4'd7;\n"
      "    #0 b = 4'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// The static deferred assertion's label is the block identifier of the
// implicit procedure, so the default $error of a failing one names the scope
// m.a1 and the statement's own line, as §20.10 has the report carry.
TEST(StaticDeferredAssertionSim, ModuleLevelDeferredAssertNamesItsLabel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b1;\n"
      "  a1: assert #0 (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityScope(), "m.a1");
  EXPECT_EQ(f.ctx.LastSeverityLine(), 4u);
}

}  // namespace
