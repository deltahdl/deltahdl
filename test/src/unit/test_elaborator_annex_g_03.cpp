#include <gtest/gtest.h>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(SemaphoreStdPackageElaborator, AContainerOfSemaphoresTakesItsOwnMethods) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  semaphore q[$];\n"
      "  semaphore a[];\n"
      "  semaphore t;\n"
      "  initial begin\n"
      "    t = new(1);\n"
      "    q.push_back(t);\n"
      "    if (a.size() == 2) t.peek();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'semaphore' declares no method 'peek'", 8,
                            "G.3"));
  for (const auto& d : f.diag.Diagnostics()) EXPECT_NE(d.loc.line, 7u);
}

}  // namespace
