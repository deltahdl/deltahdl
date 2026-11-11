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

TEST(ClassSim, WeakRefE2eStdScopedBlockDeclarationIsTheBuiltinClass) {
  EXPECT_EQ(RunAndGet("class obj; int v = 9; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static obj strong_obj = new;\n"
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

TEST(ClassSim,
     WeakReferenceToASpecializationInterfaceClassOrWeakReferenceRuns) {
  SimFixture f;
  std::string out = RunCapture(
      "class C #(int N = 1); int x = N; endclass\n"
      "typedef C #(4) c4_t;\n"
      "interface class I; pure virtual function int g(); endclass\n"
      "class K implements I; virtual function int g(); return 3; endfunction "
      "endclass\n"
      "class D; int x = 7; endclass\n"
      "module m;\n"
      "  weak_reference #(C #(4)) w1;\n"
      "  weak_reference #(c4_t) w2;\n"
      "  weak_reference #(I) w3;\n"
      "  weak_reference #(weak_reference #(D)) w4;\n"
      "  C #(4) c;\n"
      "  K k;\n"
      "  D d;\n"
      "  weak_reference #(D) wd;\n"
      "  int r1, r2, r3, r4;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    w1 = new(c);\n"
      "    w2 = new(c);\n"
      "    k = new;\n"
      "    w3 = new(k);\n"
      "    d = new;\n"
      "    wd = new(d);\n"
      "    w4 = new(wd);\n"
      "    r1 = w1.get().x;\n"
      "    r2 = w2.get().x;\n"
      "    r3 = w3.get().g();\n"
      "    r4 = (w4.get() == wd);\n"
      "    $display(\"%0d %0d %0d %0d\", r1, r2, r3, r4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "4 4 3 1\n");
}

TEST(ClassSim, DISABLED_UserClassNamedWeakReferenceInAModuleShadowsTheBuiltIn) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "module m;\n"
      "  class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "  C h;\n"
      "  weak_reference #(int) w = new(5);\n"
      "  std::weak_reference #(C) s;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    s = new(h);\n"
      "    r1 = w.v;\n"
      "    r2 = (s.get() == h);\n"
      "    $display(\"%0d %0d\", r1, r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "5 1\n");
}

TEST(
    ClassSim,
    DISABLED_UserClassNamedWeakReferenceImportedFromAPackageShadowsTheBuiltIn) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "package p;\n"
      "  class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::weak_reference;\n"
      "  C h;\n"
      "  weak_reference #(int) w = new(5);\n"
      "  std::weak_reference #(C) s;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    s = new(h);\n"
      "    $display(\"%0d %0d\", w.v, s.get() == h);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "5 1\n");
}

TEST(ClassSim, DISABLED_UserClassNamedWeakReferenceNamedThroughItsPackage) {
  SimFixture f;
  std::string out = RunCapture(
      "package p;\n"
      "  class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "endpackage\n"
      "module m;\n"
      "  p::weak_reference #(int) w = new(6);\n"
      "  initial $display(\"%0d\", w.v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "6\n");
}

TEST(
    ClassSim,
    DISABLED_UserClassNamedWeakReferenceInTheCompilationUnitShadowsTheBuiltIn) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int x = 7; endclass\n"
      "class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "module m;\n"
      "  C h;\n"
      "  weak_reference #(int) w = new(5);\n"
      "  std::weak_reference #(C) s;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    s = new(h);\n"
      "    $display(\"%0d %0d\", w.v, s.get() == h);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "5 1\n");
}

TEST(ClassSim,
     DISABLED_UserClassNamedWeakReferenceInAnInterfaceShadowsTheBuiltIn) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc;\n"
      "  class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "  weak_reference #(int) w = new(5);\n"
      "endinterface\n"
      "module m;\n"
      "  ifc i ();\n"
      "  initial #1 $display(\"%0d\", i.w.v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "5\n");
}

TEST(ClassSim,
     DISABLED_UserClassNamedWeakReferenceInAProgramShadowsTheBuiltIn) {
  SimFixture f;
  std::string out = RunCapture(
      "program prg;\n"
      "  class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "  weak_reference #(int) w = new(6);\n"
      "  initial $display(\"%0d\", w.v);\n"
      "endprogram\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "6\n");
}

}  // namespace
