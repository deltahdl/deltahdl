#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"

// §16.4.3 "Deferred assertions outside procedural code".
//
// A deferred immediate assertion written outside any procedure (as a module
// item) is a "static deferred assertion" and is treated as if it were the sole
// statement of an always_comb procedure. The elaborator carries this rule by
// synthesizing an implicit always_comb process around the assertion
// (elaborator_items.cpp, IsStaticDeferredAssertion), so at run time the
// assertion inherits always_comb behaviour: it is evaluated once after the
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
      "  a1: assert #0 (a == b) else fires = fires + 1;\n"
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
      "  a1: assert #0 (a == b) else fires = fires + 1;\n"
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

}  // namespace
