#include <gtest/gtest.h>

#include <string>

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

// §8.30.2's example (printed page 218 of ~/IEEE 1800-2023.pdf) read whole
// through the production pipeline, the two references declared as one
// module-scope declarator list with the `#` against the class name, and every
// method of §8.30.1's list (printed 217-219) called on them in one run: the two
// instances are distinct objects (§8.30.2) referring to one referent, get()
// answers the referent (§8.30.3) whose property initializer is read back
// through it, clear() sets get() to null (§8.30.4), and get_id() answers 0
// for null, one value for one object whichever class the specialization
// names, and a nonzero value otherwise (§8.30.5). The example's names weak1
// and weak2 are Table B.1's reserved drive strengths (printed 1220), which
// §5.6 (printed 74) keeps out of user-defined identifiers, so the references
// are named wref1 and wref2 here. Every line is a distinct printed value, so
// a reference that ran on nothing shows in the output where it stood.
TEST(ClassSim, WeakRefE2eModuleScopeDeclaratorListRunsEveryMethod) {
  SimFixture f;
  std::string out = RunCapture(
      "class obj; int v = 9; endclass\n"
      "class ex_obj extends obj; endclass\n"
      "module t;\n"
      "  obj strong_obj, got;\n"
      "  weak_reference#(obj) wref1, wref2;\n"
      "  initial begin\n"
      "    strong_obj = new;\n"
      "    wref1 = new(strong_obj); wref2 = new(strong_obj);\n"
      "    $display(\"neq %0d\", wref1 != wref2);\n"
      "    $display(\"same %0d\", wref1.get() == wref2.get());\n"
      "    got = wref1.get();\n"
      "    $display(\"v %0d\", got.v);\n"
      "    wref1.clear();\n"
      "    $display(\"cleared %0d\", wref1.get() == null);\n"
      "    $display(\"id0 %0d\", weak_reference#(obj)::get_id(null));\n"
      "    $display(\"idsame %0d\", weak_reference#(obj)::get_id(strong_obj) "
      "== weak_reference#(ex_obj)::get_id(strong_obj));\n"
      "    $display(\"idnz %0d\", weak_reference#(obj)::get_id(strong_obj) "
      "!= 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "neq 1\nsame 1\nv 9\ncleared 1\nid0 0\nidsame 1\nidnz 1\n");
}

}  // namespace
