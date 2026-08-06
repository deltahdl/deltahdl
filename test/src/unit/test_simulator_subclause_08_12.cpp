#include <memory>
#include <unordered_set>

#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassAssignRenameSim, ShallowCopyCopiesRngState) {
  SimFixture f;
  auto* type = MakeClassType(f, "R", {"x"});
  auto [h, obj] = MakeObj(f, type);
  obj->rng_seed = 0xC0FFEEu;
  obj->rng_initialized = true;
  obj->rng.seed(obj->rng_seed);
  // Advance the generator so its live state diverges from a freshly seeded one.
  (void)obj->rng();
  (void)obj->rng();

  auto* copy = obj->ShallowCopy(f.arena);
  EXPECT_EQ(copy->rng_seed, 0xC0FFEEu);
  EXPECT_TRUE(copy->rng_initialized);
  // The copy resumes the source's generator state, not a fresh one.
  EXPECT_EQ(copy->rng, obj->rng);
}

TEST(ClassAssignRenameSim, E2eShallowCopyDoesNotRerunFieldInitializer) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x = 7;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 42;\n"
      "    p2 = new p1;\n"
      "    result = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  // The shallow copy preserves the mutated value; the `x = 7` declaration
  // initializer is not re-executed during the copy's allocation.
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, ShallowCopyPreservesDerivedType) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"j"});
  auto* ext = MakeClassType(f, "Ext", {"x"});
  ext->parent = base;

  auto [h, obj] = MakeObj(f, ext);
  obj->SetProperty("j", MakeLogic4VecVal(f.arena, 32, 5));
  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 9));

  auto* copy = obj->ShallowCopy(f.arena);
  EXPECT_EQ(copy->type, ext);
  EXPECT_EQ(copy->GetProperty("j", f.arena).ToUint64(), 5u);
  EXPECT_EQ(copy->GetProperty("x", f.arena).ToUint64(), 9u);
}

TEST(ClassAssignRenameSim, E2eHandleAssignmentAliasesObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 10;\n"
      "    p2 = p1;\n"
      "    p2.x = 42;\n"
      "    result = p1.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyCopiesProperties) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C p1, p2;\n"
                      "    p1 = new;\n"
                      "    p1.x = 42;\n"
                      "    p2 = new p1;\n"
                      "    result = p2.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ClassAssignRenameSim, E2eShallowCopyCreatesIndependentObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 10;\n"
      "    p2 = new p1;\n"
      "    p2.x = 99;\n"
      "    r1 = p1.x;\n"
      "    r2 = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 99u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyDoesNotCallConstructor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "    x = 999;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 42;\n"
      "    p2 = new p1;\n"
      "    result = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopySharesNestedHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Inner;\n"
      "  int val;\n"
      "endclass\n"
      "class Outer;\n"
      "  int x;\n"
      "  Inner a;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Outer o1, o2;\n"
      "    o1 = new;\n"
      "    o1.a = new;\n"
      "    o1.a.val = 77;\n"
      "    o2 = new o1;\n"
      "    r1 = o2.a.val;\n"
      "    o2.a.val = 88;\n"
      "    r2 = o1.a.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 77u}, {"r2", 88u}});
}

TEST(ClassAssignRenameSim, E2eChainedMemberAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  int j;\n"
      "endclass\n"
      "class B;\n"
      "  int i;\n"
      "  A a;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    B b1;\n"
      "    b1 = new;\n"
      "    b1.i = 1;\n"
      "    b1.a = new;\n"
      "    b1.a.j = 50;\n"
      "    r1 = b1.i;\n"
      "    r2 = b1.a.j;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 50u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyWithInheritance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  int j;\n"
      "endclass\n"
      "class Ext extends Base;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Ext e;\n"
      "    Base b;\n"
      "    e = new;\n"
      "    e.j = 5;\n"
      "    e.x = 9;\n"
      "    b = e;\n"
      "    Base b2;\n"
      "    b2 = new b;\n"
      "    r1 = b2.j;\n"
      "    r2 = b.j;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 5u}, {"r2", 5u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyMultipleProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a;\n"
      "  int b;\n"
      "  int c;\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb, rc;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.a = 1;\n"
      "    p1.b = 2;\n"
      "    p1.c = 3;\n"
      "    p2 = new p1;\n"
      "    ra = p2.a;\n"
      "    rb = p2.b;\n"
      "    rc = p2.c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 1u}, {"rb", 2u}, {"rc", 3u}});
}

// §8.12: a shallow copy duplicates all of the source's variables, and the LRM
// names strings alongside integers and handles among them. This drives a real
// `string`-typed property through the full pipeline (rather than a hand-packed
// value): the string is carried into the copy, and because a string is a value
// variable (not a shared object handle), rewriting the source afterward leaves
// the copy's string unchanged.
TEST(ClassAssignRenameSim, E2eShallowCopyCopiesStringProperty) {
  const char* src =
      "class C;\n"
      "  string s;\n"
      "endclass\n"
      "module t;\n"
      "  int copied;\n"
      "  int independent;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.s = \"hello\";\n"
      "    p2 = new p1;\n"
      "    copied = (p2.s == \"hello\") ? 1 : 0;\n"
      "    p1.s = \"world\";\n"
      "    independent = (p2.s == \"hello\") ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "copied"), 1u);
  EXPECT_EQ(RunAndGet(src, "independent"), 1u);
}

// §8.12 (shallow copy, step 2): the internal states used for randomization are
// copied to the new object. Among them is the rand_mode status of random
// variables (§18.8). Disabling a variable's rand_mode on the source and then
// shallow-copying must carry the disabled status into the copy, while an
// independently constructed object still reports the default active status.
// The mode is read back through the LRM query form, so this observes the copied
// state directly rather than inferring it from a randomization outcome.
TEST(ClassAssignRenameSim, E2eShallowCopyCopiesRandModeStatus) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int copied;\n"
      "  int fresh;\n"
      "  initial begin\n"
      "    C p1, p2, p3;\n"
      "    p1 = new;\n"
      "    p1.x.rand_mode(0);\n"
      "    p2 = new p1;\n"
      "    copied = p2.x.rand_mode();\n"
      "    p3 = new;\n"
      "    fresh = p3.x.rand_mode();\n"
      "  end\n"
      "endmodule\n";
  // The copy inherited the source's disabled rand_mode (0); a fresh object is
  // still active (1), proving the 0 came from the copy rather than a default.
  EXPECT_EQ(RunAndGet(src, "copied"), 0u);
  EXPECT_EQ(RunAndGet(src, "fresh"), 1u);
}

// §8.12 (shallow copy, step 2): the constraint_mode status of constraints
// (§18.9) is likewise part of the copied randomization state. Turning a named
// block off on the source and shallow-copying carries the off status into the
// copy, while a separately constructed object still reports the block active.
TEST(ClassAssignRenameSim, E2eShallowCopyCopiesConstraintModeStatus) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x < 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int copied;\n"
      "  int fresh;\n"
      "  initial begin\n"
      "    C p1, p2, p3;\n"
      "    p1 = new;\n"
      "    p1.c.constraint_mode(0);\n"
      "    p2 = new p1;\n"
      "    copied = p2.c.constraint_mode();\n"
      "    p3 = new;\n"
      "    fresh = p3.c.constraint_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "copied"), 0u);
  EXPECT_EQ(RunAndGet(src, "fresh"), 1u);
}

// §8.12 (shallow copy, step 2): the cyclic state of randc variables (§18.4.2)
// is among the copied randomization state, and it must be copied as an
// independent per-object cycle rather than shared with the source -- each
// object advances its own permutation. This state is internal (no source-level
// query exposes it), so the copy operation is exercised directly, mirroring the
// existing ShallowCopyCopiesRngState unit test. The independence check (a
// mutation to the copy's history leaving the source's untouched) is the visible
// proof that the fix clones the set rather than aliasing the shared handle.
TEST(ClassAssignRenameSim, ShallowCopyCopiesRandcCyclicStateIndependently) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"y"});
  auto [h, obj] = MakeObj(f, type);
  auto history = std::make_shared<std::unordered_set<int64_t>>();
  history->insert(0);
  history->insert(1);
  obj->randc_history["y"] = history;

  auto* copy = obj->ShallowCopy(f.arena);

  // The in-progress permutation carried across to the copy.
  ASSERT_TRUE(copy->randc_history.count("y"));
  EXPECT_EQ(copy->randc_history["y"]->size(), 2u);
  EXPECT_TRUE(copy->randc_history["y"]->count(0));
  EXPECT_TRUE(copy->randc_history["y"]->count(1));

  // Advancing the copy's cycle does not disturb the source's cycle: the two
  // objects own independent cyclic state.
  copy->randc_history["y"]->insert(2);
  EXPECT_EQ(obj->randc_history["y"]->size(), 2u);
  EXPECT_FALSE(obj->randc_history["y"]->count(2));
}

// §8.12: the shallow-copy form `new src` may also appear as a declaration
// initializer (`C c2 = new c1;`), a distinct syntactic position from the
// procedural `c2 = new c1;` assignment and served by a separate runtime
// dispatch path. Driving the decl-initializer form through the full pipeline
// confirms that path copies the source object's properties too.
TEST(ClassAssignRenameSim, E2eDeclInitShallowCopyCopiesProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c1;\n"
      "    c1 = new;\n"
      "    c1.x = 55;\n"
      "    C c2 = new c1;\n"
      "    result = c2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 55u}});
}

// §8.12: renaming (a plain handle copy that aliases the same object) likewise
// has a declaration-initializer position (`C p2 = p1;`) distinct from the
// procedural `p2 = p1;`. The decl-init copy shares the object, so a write
// through the new name is visible through the original.
TEST(ClassAssignRenameSim, E2eDeclInitHandleAssignmentAliasesObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1;\n"
      "    p1 = new;\n"
      "    p1.x = 33;\n"
      "    C p2 = p1;\n"
      "    p2.x = 77;\n"
      "    result = p1.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 77u}});
}

// §8.12 (shallow copy, step 2) via §18.4 randc: the cyclic state of a real
// randc variable is copied into the new object. Built from live `randc` source
// and driven through randomize() rather than a hand-populated history: a
// four-value randc drawn three times leaves one value unconsumed in the current
// permutation; the shallow copy carries that three-value history, so the copy's
// next randomize() is forced to the single remaining value -- distinct from all
// three the source already drew. Had the cyclic state not been copied, the copy
// would start a fresh permutation and could repeat one of them.
TEST(ClassAssignRenameSim, E2eShallowCopyCarriesRandcCyclicState) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b, c, d, distinct;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    ok = p1.randomize();\n"
      "    a = p1.y;\n"
      "    ok = p1.randomize();\n"
      "    b = p1.y;\n"
      "    ok = p1.randomize();\n"
      "    c = p1.y;\n"
      "    p2 = new p1;\n"
      "    ok = p2.randomize();\n"
      "    d = p2.y;\n"
      "    distinct = (d != a && d != b && d != c) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  // The copy's draw completes the source's permutation: it is the one value the
  // source had not yet drawn, so it differs from all three prior draws.
  EXPECT_EQ(RunAndGet(src, "distinct"), 1u);
}

// §8.12 (shallow copy, step 2) via §18.14 object stability: the RNG stream
// state is copied into the new object. Built from live `rand` source: after the
// source randomizes once (advancing its per-object stream), the shallow copy
// captures the stream at that point. Randomizing the source and the copy once
// more each then draws from the same captured state and yields the same value,
// which holds only because the stream state carried across (and remains
// independent -- the source advancing its own stream does not disturb the
// copy).
TEST(ClassAssignRenameSim, E2eShallowCopyCarriesRngStream) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, same;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    ok = p1.randomize();\n"
      "    p2 = new p1;\n"
      "    ok = p1.randomize();\n"
      "    ok = p2.randomize();\n"
      "    r1 = p1.x;\n"
      "    r2 = p2.x;\n"
      "    same = (r1 == r2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  // Source and copy resume from the same copied stream state, so their next
  // draws agree.
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

}  // namespace
