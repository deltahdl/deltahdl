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

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §G.3: the prototype as src/elaborator/std_package.h writes it down -- the
// constructor new and the methods put, get and try_get, put and get void, get
// the one task, try_get returning int, each with the single formal int
// keyCount carrying a default, so that a call may pass one actual or none.
TEST(SemaphoreStdPackageElaborator, ThePrototypeIsWrittenDown) {
  const auto& prototype = SemaphorePrototype();
  ASSERT_EQ(prototype.size(), 4u);
  EXPECT_EQ(prototype[0].name, "new");
  EXPECT_EQ(prototype[0].kind, StdMethodKind::kFunction);
  EXPECT_EQ(prototype[1].name, "put");
  EXPECT_EQ(prototype[1].kind, StdMethodKind::kFunction);
  EXPECT_EQ(prototype[1].return_type, "void");
  EXPECT_EQ(prototype[2].name, "get");
  EXPECT_EQ(prototype[2].kind, StdMethodKind::kTask);
  EXPECT_EQ(prototype[3].name, "try_get");
  EXPECT_EQ(prototype[3].kind, StdMethodKind::kFunction);
  EXPECT_EQ(prototype[3].return_type, "int");
  for (const StdMethodPrototype& method : prototype) {
    ASSERT_EQ(method.formals.size(), 1u);
    EXPECT_EQ(method.formals[0].type, "int");
    EXPECT_EQ(method.formals[0].name, "keyCount");
    EXPECT_TRUE(method.formals[0].has_default);
    EXPECT_FALSE(method.is_static);
    EXPECT_EQ(LeastActualsOf(method), 0u);
    EXPECT_EQ(MostActualsOf(method), 1u);
  }
  EXPECT_EQ(&StdClassPrototype(StdPackageMember::kSemaphore), &prototype);
  ASSERT_NE(StdMethodNamed(StdPackageMember::kSemaphore, "get"), nullptr);
  EXPECT_EQ(StdMethodNamed(StdPackageMember::kSemaphore, "get")->kind,
            StdMethodKind::kTask);
  EXPECT_EQ(StdMethodNamed(StdPackageMember::kSemaphore, "peek"), nullptr);
  EXPECT_TRUE(StdClassPrototype(StdPackageMember::kRandomize).empty());
}

// §G.3: a call on a semaphore handle of a method the prototype does not
// declare is rejected, at the call, under the subclause giving the
// prototype; the prototype's own methods are accepted beside it.
TEST(SemaphoreStdPackageElaborator, AMethodOutsideThePrototypeIsRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem = new(2);\n"
      "    sem.put(1);\n"
      "    sem.peek();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'semaphore' declares no method 'peek'", 6,
                            "G.3"));
}

// §G.3: each method has the one formal keyCount, so a call passing two
// actuals is rejected, at the call, whether the handle is a module variable
// or one a procedural block declares, while a call passing one or none is
// accepted; the count reported is the one given.
TEST(SemaphoreStdPackageElaborator, ACallWithMoreActualsThanFormalsIsRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    semaphore local_sem;\n"
      "    sem.put(1, 2);\n"
      "    sem.get();\n"
      "    local_sem.get(1, 2, 3);\n"
      "    if (sem.try_get(1)) sem.put();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'put' of class 'semaphore' takes at most 1 "
                            "argument; 2 given",
                            5, "G.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' of class 'semaphore' takes at most 1 "
                            "argument; 3 given",
                            7, "G.3"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, 6u);
    EXPECT_NE(d.loc.line, 8u);
  }
}

}  // namespace
