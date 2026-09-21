#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakReferenceDoesNotPreventGc) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, WeakReferenceClearedWhenReferentCollected) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, MultipleWeakRefsClearedAtomically) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr1;
  wr1.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr1);
  WeakReference wr2;
  wr2.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr2);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

  EXPECT_EQ(wr1.Get(), kNullClassHandle);
  EXPECT_EQ(wr2.Get(), kNullClassHandle);
}

// §8.30/§8.29: an instance of the built-in weak_reference class is itself an
// ordinary heap object and is therefore garbage-collection eligible -- once its
// last strong handle is dropped and it becomes unreachable, the collector
// reclaims it. A separate, still strongly reachable object is spared. Per §8.29
// an object is strongly reachable only when a class handle refers to it in an
// active scope (or a pending NBA / the creating process holds it); the
// auxiliary ref count is not part of that definition, so the spared object must
// be rooted in a live variable to be genuinely strongly reachable.
TEST(ClassSim, WeakReferenceInstanceIsGcEligible) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto* strong = f.ctx.CreateVariable("strong", 64);
  f.ctx.SetVariableClassType("strong", "obj");
  strong->value = MakeLogic4VecVal(f.arena, 64, handle);

  auto* wr_type = MakeClassType(f, "weak_reference", {"referent_handle"});
  auto [wr_handle, wr_obj] = MakeObj(f, wr_type);

  f.ctx.ReleaseObject(wr_handle);
  f.ctx.CollectGarbage();

  EXPECT_EQ(f.ctx.GetClassObject(wr_handle), nullptr);
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
}

// §8.30.1 (printed page 218 of IEEE 1800-2023) puts the weak_reference
// class in the built-in std package of §26.7 (printed 816), which §26.3 reaches
// through the package scope resolution operator, so `std::weak_reference#(obj)`
// at module scope declares the same class as the bare name: the run constructs
// it with new(referent) (§8.30.2), reads the referent's property through get()
// (§8.30.3) and has clear() set get() to null (§8.30.4). A declaration the
// package scope turned into something other than the built-in class would
// construct no weak reference, and the two printed values would not both be
// read.
TEST(ClassSim, WeakRefE2eStdScopedModuleScopeDeclarationIsTheBuiltinClass) {
  SimFixture f;
  std::string out = RunCapture(
      "class obj; int v = 9; endclass\n"
      "module t;\n"
      "  obj strong_obj, got;\n"
      "  std::weak_reference#(obj) wref1;\n"
      "  initial begin\n"
      "    strong_obj = new;\n"
      "    wref1 = new(strong_obj);\n"
      "    got = wref1.get();\n"
      "    $display(\"v %0d\", got.v);\n"
      "    wref1.clear();\n"
      "    $display(\"cleared %0d\", wref1.get() == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "v 9\ncleared 1\n");
}

// The same package-scoped declaration as a block item of the initial
// procedure (A.2.8), where the procedural declaration path rather than the
// lowerer creates the variable: get() answers the referent, so the property
// read through it is 9, and after clear() the reference answers null, so the
// packed result is 9 * 10 + 1.
TEST(ClassSim, WeakRefE2eStdScopedBlockDeclarationIsTheBuiltinClass) {
  EXPECT_EQ(RunAndGet("class obj; int v = 9; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj = new;\n"
                      "    obj got;\n"
                      "    std::weak_reference#(obj) wref1;\n"
                      "    wref1 = new(strong_obj);\n"
                      "    got = wref1.get();\n"
                      "    result = got.v * 10;\n"
                      "    wref1.clear();\n"
                      "    result = result + (wref1.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            91u);
}

// §8.30.1 (printed page 217 of IEEE 1800-2023) with §26.2 (printed 808):
// a package's `weak_reference #(C) w = new(h);` is the declaration assignment
// that creates the weak reference to the object the package's earlier `C h
// = new;` constructed, made before any procedure starts, so a module's
// `p::w.get()` (§8.30.3) answers that object and its v reads 3. The
// package's constructions skipped a class the run holds no record of, the
// built-in weak_reference among them, whose new(obj) the procedural
// assignment alone took (AssignWeakReferenceNew in
// statement_assign_object.cpp), so nothing was created, get() answered null
// and y stayed 0.
TEST(ClassSim, PackageWeakReferenceDeclarationInitializerRefersToTheObject) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    int v = 3;\n"
                      "  endclass\n"
                      "  C h = new;\n"
                      "  weak_reference #(C) w = new(h);\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  C c;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    c = p::w.get();\n"
                      "    y = c.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

// The referent is the package's own handle: `p::w.get() == p::h` reads 1,
// and `p::h != null` 1 beside it, so y is 11. A weak reference to nothing
// answers null, unequal to the constructed h: 10; h constructed by nothing
// and w by nothing would compare two nulls equal: 1.
TEST(ClassSim, PackageWeakReferenceGetAnswersThePackagesOwnHandle) {
  EXPECT_EQ(
      RunAndGet("package p;\n"
                "  class C;\n"
                "    int v = 3;\n"
                "  endclass\n"
                "  C h = new;\n"
                "  weak_reference #(C) w = new(h);\n"
                "endpackage\n"
                "module top;\n"
                "  int y;\n"
                "  initial y = (p::h != null) * 10 + (p::w.get() == p::h);\n"
                "endmodule\n",
                "y"),
      11u);
}

// §3.12.1 (printed page 56) with §8.30.1: the same two declarations outside
// every module are the compilation unit's, constructed by the one path the
// package's are (ConstructDataClassInitializers), so a module's `w.get()`
// answers the unit's object and y reads 3.
TEST(ClassSim, UnitWeakReferenceDeclarationInitializerRefersToTheObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v = 3;\n"
                      "endclass\n"
                      "C h = new;\n"
                      "weak_reference #(C) w = new(h);\n"
                      "module top;\n"
                      "  C c;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    c = w.get();\n"
                      "    y = c.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

// §8.30.1 (printed page 217 of IEEE 1800-2023) with §6.21 (printed
// 132-133): a module's `weak_reference #(C) w = new(h);` is a declaration
// assignment made at the declaration, ahead of the module's procedures,
// creating the weak reference to the object the module's earlier `C h = new;`
// constructed, so `w.get()` answers that object and its v reads 3. The
// module's class-typed initializer (TryLowerClassNewVarInit in
// lowerer_var.cpp) constructed by EvalClassNew alone, which holds no record
// of the built-in weak_reference class and made nothing, so get() answered
// null; the package's and the unit's declaration form had been given the
// weak reference's own new(obj) (EvalWeakReferenceNew) while the module's
// had not.
TEST(ClassSim, ModuleWeakReferenceDeclarationInitializerRefersToTheObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v = 3;\n"
                      "endclass\n"
                      "module top;\n"
                      "  C h = new;\n"
                      "  weak_reference #(C) w = new(h);\n"
                      "  C c;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    c = w.get();\n"
                      "    y = c.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

// The referent is the module's own handle: `w.get() == h` reads 1 beside
// `h != null`, 1, so y is 11. A weak reference to nothing answers null,
// unequal to the constructed h: 10.
TEST(ClassSim, ModuleWeakReferenceGetAnswersTheModulesOwnHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v = 3;\n"
                      "endclass\n"
                      "module top;\n"
                      "  C h = new;\n"
                      "  weak_reference #(C) w = new(h);\n"
                      "  int y;\n"
                      "  initial y = (h != null) * 10 + (w.get() == h);\n"
                      "endmodule\n",
                      "y"),
            11u);
}

}  // namespace
