#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- §8.30.2 observed through the full pipeline ------------------------------
//
// §8.30.2's rules govern the new() constructor, whose behavior depends on how
// the referent is produced (a real §8.4/§8.7 `new()` handle) and on the
// syntactic position the weak reference is built in (a procedural
// `wr = new(referent)` assignment vs. a declaration initializer
// `weak_reference#(T) wr = new(referent)`). The tests below build both forms
// from source and drive them through parse, elaborate, lower, and run,
// observing the production new()/get() paths rather than a hand-built wrapper.

// §8.30.2 prototype new(T referent): the constructor records the referent
// handed to it. Built via a procedural assignment; the recorded value is
// observed by querying get() and comparing it to the original strong handle.
TEST(ClassSim, WeakRefE2eNewRecordsReferentProcedural) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    result = (wr.get() == strong_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.2 prototype new(T referent), declaration-initializer position: the same
// recording rule applies when the weak reference is constructed in its own
// declaration. This drives the decl-init production path.
TEST(ClassSim, WeakRefE2eNewRecordsReferentDeclInit) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj = new();\n"
                      "    weak_reference #(obj) wr = new(strong_obj);\n"
                      "    result = (wr.get() == strong_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.2: a null referent passed to new() is accepted and recorded as null, so
// get() queries as null. Built from source through the full pipeline.
TEST(ClassSim, WeakRefE2eNewNullReferentGetsNull) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    weak_reference #(obj) wr;\n"
                      "    wr = new(null);\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.2: passing null to new() issues no warning. Observed by running a
// design that constructs a weak reference over a null referent and checking
// that the production path emitted no diagnostics.
TEST(ClassSim, WeakRefE2eNewNullNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class obj;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    weak_reference #(obj) wr;\n"
      "    wr = new(null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §8.30.2 null referent in declaration-initializer position: constructing the
// weak reference in its own declaration with a null referent records null (so
// get() queries as null) and still issues no warning. This drives the decl-init
// production path, distinct from the procedural-assignment path exercised
// above.
TEST(ClassSim, WeakRefE2eNewNullReferentDeclInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class obj;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    weak_reference #(obj) wr = new(null);\n"
      "    result = (wr.get() == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §8.30.2 uniqueness (the LRM example): two weak references built from the same
// referent are distinct objects (their handles compare unequal), yet get()
// returns the same referent for both. Both weak references are constructed from
// real new(referent) source.
TEST(ClassSim, WeakRefE2eInstancesUniqueButSameReferent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class obj;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int distinct;\n"
      "  int same_referent;\n"
      "  initial begin\n"
      "    obj strong_obj;\n"
      "    weak_reference #(obj) wref1, wref2;\n"
      "    strong_obj = new();\n"
      "    wref1 = new(strong_obj);\n"
      "    wref2 = new(strong_obj);\n"
      "    distinct = (wref1 != wref2);\n"
      "    same_referent = (wref1.get() == wref2.get());\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"distinct", 1u}, {"same_referent", 1u}});
}

}  // namespace
