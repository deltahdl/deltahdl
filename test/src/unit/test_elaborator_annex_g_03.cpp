// IEEE 1800-2023 Annex G.3 (Std package -- Semaphore).
//
// Section G.3 presents the prototype of the built-in `semaphore` class that
// the std package provides; its semantics are owned by clause 15.3. The
// prototype is:
//
//   class semaphore;
//     function new(int keyCount = 0);
//     function void put(int keyCount = 1);
//     task get(int keyCount = 1);
//     function int try_get(int keyCount = 1);
//   endclass
//
// These tests observe the elaborator providing that prototype out of the std
// package: `semaphore` resolves as a built-in class without any user
// `class semaphore` definition (Elaborator::RegisterCuScopeItems registers the
// std-package class name), and each prototype method elaborates with the
// documented default arguments omitted at the call site.

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The std package supplies the class name; no user declaration is required.
TEST(SemaphoreStdPackageElaborator, BuiltInClassNeedsNoUserDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "semaphore");
}

// new() with the keyCount argument omitted (prototype default 0).
TEST(SemaphoreStdPackageElaborator, NewWithDefaultKeyCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "semaphore");
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

// The full prototype surface: put / get / try_get, each invoked with the
// documented default keyCount omitted.
TEST(SemaphoreStdPackageElaborator, PrototypeMethodsWithDefaultArgs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new();\n"
      "  int got;\n"
      "  initial begin\n"
      "    sem.put();\n"
      "    sem.get();\n"
      "    got = sem.try_get();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The same prototype methods accept an explicit keyCount, matching the
// `int keyCount` formals in the prototype.
TEST(SemaphoreStdPackageElaborator, PrototypeMethodsWithExplicitArgs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new(2);\n"
      "  int got;\n"
      "  initial begin\n"
      "    sem.put(2);\n"
      "    sem.get(1);\n"
      "    got = sem.try_get(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The prototype's new() constructor also applies when the handle is built
// procedurally after declaration, then driven through the prototype methods.
TEST(SemaphoreStdPackageElaborator, DeferredConstructionAndUse) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem = new(2);\n"
      "    sem.get();\n"
      "    sem.put();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// try_get is `function int`: its value feeds an expression context (here an
// if-condition), and the elaborator accepts the value-returning prototype
// method there.
TEST(SemaphoreStdPackageElaborator, TryGetResultUsableInCondition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new();\n"
      "  initial begin\n"
      "    if (sem.try_get()) sem.put();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
