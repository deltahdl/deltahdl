#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

void ExpectReported(const std::string& src, std::string_view message,
                    std::string_view at, std::string_view subclause) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, LineHolding(src, at),
                            subclause))
      << src;
}

std::string InAModule(const std::string& statement) {
  return "module m;\n"
         "  semaphore s = new(1);\n"
         "  int x;\n"
         "  initial begin\n"
         "    " +
         statement +
         "\n"
         "  end\n"
         "endmodule\n";
}

std::string InAClass(const std::string& statement) {
  return "class c;\n"
         "  semaphore s;\n"
         "  int x;\n"
         "  function void f();\n"
         "    " +
         statement +
         "\n"
         "  endfunction\n"
         "endclass\n"
         "module m;\n"
         "endmodule\n";
}

std::string InAPackage(const std::string& statement) {
  return "package k;\n"
         "  int x;\n"
         "  function automatic void f(semaphore s);\n"
         "    " +
         statement +
         "\n"
         "  endfunction\n"
         "endpackage\n"
         "module m;\n"
         "endmodule\n";
}

TEST(SemaphoreStdPackageElaborator, TheConstructorTakesAtMostOneActual) {
  EXPECT_TRUE(ElabOk(InAModule("s = new(1);")));
  ExpectReported(InAModule("s = new(1, 2);"),
                 "constructor of class 'semaphore' takes at most 1 argument; 2 "
                 "given",
                 "new(1, 2)", "G.3");
}

TEST(SemaphoreStdPackageElaborator, TryGetTakesAtMostOneActual) {
  EXPECT_TRUE(ElabOk(InAModule("x = s.try_get(1);")));
  ExpectReported(InAModule("x = s.try_get(1, 2);"),
                 "method 'try_get' of class 'semaphore' takes at most 1 "
                 "argument; 2 given",
                 "try_get", "G.3");
}

TEST(SemaphoreStdPackageElaborator,
     DISABLED_AnExcessActualIsRejectedInAClassAndAPackage) {
  EXPECT_TRUE(ElabOk(InAClass("s.put(1);")));
  EXPECT_TRUE(ElabOk(InAPackage("s.put(1);")));
  for (const auto& src :
       {InAClass("s.put(1, 2);"), InAPackage("s.put(1, 2);")}) {
    ExpectReported(src,
                   "method 'put' of class 'semaphore' takes at most 1 "
                   "argument; 2 given",
                   "s.put", "G.3");
  }
}

TEST(SemaphoreStdPackageElaborator, AVoidCastDiscardsTheResultOfTryGet) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(InAModule("void'(s.try_get());"), f));
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(SemaphoreStdPackageElaborator, PutIsAStatement) {
  EXPECT_TRUE(ElabOk(InAModule("s.put(1);")));
  EXPECT_TRUE(ElabOk(InAClass("s.put(1);")));
  EXPECT_TRUE(ElabOk(InAPackage("s.put(1);")));
}

TEST(SemaphoreStdPackageElaborator, DISABLED_PutIsNoOperand) {
  for (const auto& src :
       {InAModule("x = s.put(1);"), InAModule("if (s.put(1)) x = 1;"),
        InAClass("x = s.put(1);"), InAPackage("x = s.put(1);")}) {
    ExpectReported(src, "void function 'put' used as expression operand",
                   "s.put", "13.4.1");
  }
}

TEST(SemaphoreStdPackageElaborator, DISABLED_GetIsNoOperand) {
  EXPECT_TRUE(ElabOk(InAModule("s.get(1);")));
  for (const char* statement : {"x = s.get(1);", "if (s.get(1)) x = 1;"}) {
    ExpectReported(InAModule(statement),
                   "task 'get' is enabled from a statement and cannot be an "
                   "operand of an expression",
                   "s.get", "13.3");
  }
}

TEST(SemaphoreStdPackageElaborator, AForkedGetInAFunctionIsAccepted) {
  const std::string kForked = "fork s.get(1); join_none";
  EXPECT_TRUE(ElabOk(InAClass(kForked)));
  EXPECT_TRUE(ElabOk(InAPackage(kForked)));
}

TEST(SemaphoreStdPackageElaborator, DISABLED_AFunctionEnablesNoGet) {
  const std::string kInAModuleFunction =
      "module m;\n"
      "  semaphore s = new(1);\n"
      "  function void f();\n"
      "    s.get(1);\n"
      "  endfunction\n"
      "endmodule\n";
  for (const auto& src :
       {kInAModuleFunction, InAClass("s.get(1);"), InAClass("this.s.get(1);"),
        InAPackage("s.get(1);")}) {
    ExpectReported(src, "function cannot enable a task", "s.get", "13.4");
  }
}

TEST(SemaphoreStdPackageElaborator,
     DISABLED_AFunctionOfADerivedClassEnablesNoInheritedGet) {
  for (const std::string kPrefix : {"", "this.", "super."}) {
    ExpectReported(
        "class d extends semaphore;\n"
        "  function void f();\n"
        "    " +
            kPrefix +
            "get(1);\n"
            "  endfunction\n"
            "endclass\n"
            "module m;\n"
            "endmodule\n",
        "function cannot enable a task", "get(1)", "13.4");
  }
}

TEST(SemaphoreStdPackageElaborator, AnActualBoundToKeyCountByNameIsAccepted) {
  for (const char* statement :
       {"s = new(.keyCount(1));", "s.put(.keyCount(1));",
        "s.get(.keyCount(1));", "x = s.try_get(.keyCount(1));"}) {
    EXPECT_TRUE(ElabOk(InAModule(statement))) << statement;
  }
}

TEST(SemaphoreStdPackageElaborator,
     DISABLED_AnActualBoundToAnotherNameIsRejected) {
  ExpectReported(InAModule("s = new(.count(1));"), "no parameter 'count' in",
                 ".count", "G.3");
  ExpectReported(InAModule("s.put(.count(1));"), "no parameter 'count' in",
                 ".count", "G.3");
  ExpectReported(InAModule("s.get(.count(1));"), "no parameter 'count' in",
                 ".count", "G.3");
  ExpectReported(InAModule("x = s.try_get(.count(1));"),
                 "no parameter 'count' in", ".count", "G.3");
}

TEST(SemaphoreStdPackageElaborator,
     AMethodOutsideThePrototypeIsRejectedInAProgram) {
  const std::string kProgram =
      "program p;\n"
      "  semaphore s = new(1);\n"
      "  initial begin\n"
      "    s.put(1);\n"
      "    s.peek();\n"
      "  end\n"
      "endprogram\n";
  ExpectReported(kProgram, "class 'semaphore' declares no method 'peek'",
                 "s.peek", "G.3");
}

TEST(SemaphoreStdPackageElaborator,
     DISABLED_AMethodOutsideThePrototypeIsRejectedOutsideAModule) {
  const std::string kOfAnObject =
      "class c;\n"
      "  semaphore s;\n"
      "endclass\n"
      "module m;\n"
      "  c o;\n"
      "  initial o.s.peek();\n"
      "endmodule\n";
  const std::string kOfTheUnit =
      "semaphore s;\n"
      "module m;\n"
      "  initial s.peek();\n"
      "endmodule\n";
  for (const auto& src : {InAClass("s.peek();"), InAPackage("s.peek();"),
                          kOfAnObject, kOfTheUnit}) {
    ExpectReported(src, "class 'semaphore' declares no method 'peek'", "s.peek",
                   "G.3");
  }
}

TEST(SemaphoreStdPackageElaborator,
     DISABLED_AMethodOutsideThePrototypeAndTheDerivedClassIsRejected) {
  const std::string kClass =
      "class d extends semaphore;\n"
      "  function void extra();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  d s;\n"
      "  initial begin\n"
      "    s.extra();\n"
      "    s.put(1);\n";
  EXPECT_TRUE(ElabOk(kClass + "  end\nendmodule\n"));
  ExpectReported(kClass + "    s.peek();\n  end\nendmodule\n",
                 "declares no method 'peek'", "s.peek", "G.3");
}

TEST(SemaphoreStdPackageElaborator, ATypeWithoutParameterValuesIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class d extends semaphore;\n"
             "endclass\n"
             "module m;\n"
             "  semaphore s;\n"
             "  std::semaphore t;\n"
             "  mailbox #(int) b;\n"
             "endmodule\n"));
}

TEST(SemaphoreStdPackageElaborator, DISABLED_ATypeTakesNoParameterValue) {
  for (const std::string kDeclaration :
       {"semaphore #(int) s;", "std::semaphore #(int) s;"}) {
    ExpectReported("module m;\n  " + kDeclaration + "\nendmodule\n",
                   "class 'semaphore' declares no parameter", "#(int)", "G.3");
  }
  ExpectReported(
      "class d extends semaphore #(int);\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "class 'semaphore' declares no parameter", "#(int)", "G.3");
}

}  // namespace
