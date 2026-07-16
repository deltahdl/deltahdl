#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- §8.30.4 clear() observed through the full pipeline ----------------------
//
// §8.30.4 governs the weak_reference clear() method. Its prototype is
// `function void clear();` -- no arguments, no return value, so it appears only
// as a statement call. Its single normative effect is that clearing a weak
// reference sets the value returned by get() to null. That effect only makes
// sense relative to how the reference was produced: the referent it starts with
// comes from a real §8.30.2 new(referent), and the post-clear state is read
// back through §8.30.3 get(). Each test below therefore builds the reference
// from source, calls clear() from source (exercising the production clear
// dispatch), and observes get() -- rather than clearing a hand-built struct.

// §8.30.4 core rule: after clear() runs on a reference built over a real
// referent, get() returns null. The reference is constructed with a procedural
// new(referent) and the whole thing is driven parse/elaborate/lower/run.
TEST(ClassSim, WeakRefE2eClearSetsGetToNull) {
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
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.4 contrast/negative form: clear() is what causes the transition. Before
// the call, get() returns the referent; after the single clear() it returns
// null. Observing both halves in one run rules out the reference having been
// null all along -- it is the clear() call that sets get() to null.
TEST(ClassSim, WeakRefE2eClearFlipsGetFromReferentToNull) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  int before_val;\n"
                      "  int after_val;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    before_val = (wr.get() == strong_obj);\n"
                      "    wr.clear();\n"
                      "    after_val = (wr.get() == null);\n"
                      "    result = before_val & after_val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.4, declaration-initializer production form of the referent input: the
// reference is built in its own declaration (weak_reference#(T) wr =
// new(referent)), a distinct §8.30.2 syntactic position from the procedural
// assignment above. clear() still drives get() to null. Driven end to end.
TEST(ClassSim, WeakRefE2eClearSetsGetToNullDeclInit) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj = new();\n"
                      "    weak_reference #(obj) wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.4 with a null-initialized reference: clearing a reference built over a
// null referent (§8.30.2 new(null)) is safe and leaves get() returning null.
// Built from real new(null) source.
TEST(ClassSim, WeakRefE2eClearOnNullInitSafe) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    weak_reference #(obj) wr;\n"
                      "    wr = new(null);\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.4: clearing a reference twice keeps get() returning null -- the second
// clear() has nothing left to clear and does not fault. Built from source and
// driven end to end.
TEST(ClassSim, WeakRefE2eClearIdempotent) {
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
                      "    wr.clear();\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.4: clear() acts only on the reference it is called on. Two weak
// references over the same referent (the §8.30.2 weak1/weak2 form) are built;
// clearing the first drives its get() to null while the second still returns
// the referent. Both facts observed in a single run.
TEST(ClassSim, WeakRefE2eClearDoesNotAffectOtherWeakRefs) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  int first_cleared;\n"
                      "  int second_intact;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) weak1;\n"
                      "    weak_reference #(obj) weak2;\n"
                      "    strong_obj = new();\n"
                      "    weak1 = new(strong_obj);\n"
                      "    weak2 = new(strong_obj);\n"
                      "    weak1.clear();\n"
                      "    first_cleared = (weak1.get() == null);\n"
                      "    second_intact = (weak2.get() == strong_obj);\n"
                      "    result = first_cleared & second_intact;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.4: clear() clears the reference, not the referent object. After a field
// is written on the object and the reference is cleared, the object is still
// reachable through its strong handle and the field reads back unchanged.
TEST(ClassSim, WeakRefE2eClearDoesNotAffectReferent) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    strong_obj.x = 99;\n"
                      "    wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    result = strong_obj.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

}  // namespace
