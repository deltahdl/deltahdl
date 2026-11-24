#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(WeakReferenceStdPackageElaborator, BuiltInClassNeedsNoUserDefinition) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) wr;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(WeakReferenceStdPackageElaborator, TypeParameterRejectsNonClassType) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(int) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 3, "8.30.1"));
}

TEST(WeakReferenceStdPackageElaborator, TypeParameterRejectsNamedNonClassType) {
  ElabFixture f;
  ElabOk(
      "typedef enum {A, B} my_enum;\n"
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(my_enum) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 4, "8.30.1"));
}

TEST(WeakReferenceStdPackageElaborator, PrototypeInstanceMethodsElaborate) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  my_obj strong_obj;\n"
             "  my_obj result;\n"
             "  weak_reference #(my_obj) wr;\n"
             "  initial begin\n"
             "    strong_obj = new();\n"
             "    wr = new(strong_obj);\n"
             "    result = wr.get();\n"
             "    wr.clear();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(WeakReferenceStdPackageElaborator, StaticGetIdElaborates) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    my_obj o;\n"
             "    longint id;\n"
             "    o = new();\n"
             "    id = weak_reference#(my_obj)::get_id(o);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(WeakReferenceStdPackageElaborator, WeakReferenceAsSubroutineFormalType) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  function void f(weak_reference #(my_obj) wr);\n"
             "    wr.clear();\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(WeakReferenceStdPackageElaborator, ThePrototypeIsWrittenDown) {
  const auto& prototype = WeakReferencePrototype();
  ASSERT_EQ(prototype.size(), 4u);
  EXPECT_EQ(prototype[0].name, "new");
  ASSERT_EQ(prototype[0].formals.size(), 1u);
  EXPECT_EQ(prototype[0].formals[0].type, "T");
  EXPECT_EQ(prototype[0].formals[0].name, "referent");
  EXPECT_FALSE(prototype[0].formals[0].has_default);
  EXPECT_EQ(LeastActualsOf(prototype[0]), 1u);
  EXPECT_EQ(prototype[1].name, "get");
  EXPECT_EQ(prototype[1].return_type, "T");
  EXPECT_TRUE(prototype[1].formals.empty());
  EXPECT_EQ(prototype[2].name, "clear");
  EXPECT_EQ(prototype[2].return_type, "void");
  EXPECT_TRUE(prototype[2].formals.empty());
  EXPECT_EQ(prototype[3].name, "get_id");
  EXPECT_TRUE(prototype[3].is_static);
  EXPECT_EQ(prototype[3].return_type, "longint");
  ASSERT_EQ(prototype[3].formals.size(), 1u);
  EXPECT_EQ(prototype[3].formals[0].name, "obj");
  for (const StdMethodPrototype& method : prototype) {
    EXPECT_EQ(method.kind, StdMethodKind::kFunction);
  }
  EXPECT_EQ(&StdClassPrototype(StdPackageMember::kWeakReference), &prototype);
  EXPECT_TRUE(StdClassHasConstructor(StdPackageMember::kWeakReference));
  EXPECT_FALSE(StdClassIsFinal(StdPackageMember::kWeakReference));
  const StdTypeParameter kT =
      StdClassTypeParameterOf(StdPackageMember::kWeakReference)
          .value_or(StdTypeParameter{});
  EXPECT_EQ(kT.name, "T");
  EXPECT_TRUE(kT.default_type.empty());
  EXPECT_TRUE(kT.class_only);
}

TEST(WeakReferenceStdPackageElaborator,
     ConstructionsAndCallsAreCheckedAgainstThePrototype) {
  ElabFixture f;
  ElabOk(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  my_obj strong_obj;\n"
      "  my_obj result;\n"
      "  weak_reference #(my_obj) wr;\n"
      "  initial begin\n"
      "    static weak_reference #(my_obj) local_wr = new;\n"
      "    strong_obj = new();\n"
      "    wr = new;\n"
      "    wr = new(strong_obj);\n"
      "    result = wr.get(1);\n"
      "    wr.drop();\n"
      "    result = wr.get();\n"
      "    wr.clear();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constructor of class 'weak_reference' takes at "
                            "least 1 argument; 0 given",
                            9, "G.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constructor of class 'weak_reference' takes at "
                            "least 1 argument; 0 given",
                            11, "G.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' of class 'weak_reference' takes at "
                            "most 0 arguments; 1 given",
                            13, "G.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'weak_reference' declares no method 'drop'",
                            14, "G.7"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, 12u);
    EXPECT_NE(d.loc.line, 15u);
    EXPECT_NE(d.loc.line, 16u);
  }
}

std::string WeakModule(const std::string& call) {
  return "class C;\nendclass\nclass D extends C;\nendclass\nclass U;\nendclass"
         "\nmodule m;\n  C c;\n  D d;\n  U u;\n  longint id;\n"
         "  weak_reference #(C) wr;\n  initial begin\n    " +
         call + "\n  end\nendmodule\n";
}

std::string WeakMethod(const std::string& call) {
  return "class C;\nendclass\nclass D extends C;\nendclass\nclass U;\nendclass"
         "\nclass K;\n  C c;\n  weak_reference #(C) wr;\n"
         "  function void act(D d, U u);\n    longint id;\n    " +
         call + "\n  endfunction\nendclass\nmodule m;\nendmodule\n";
}

std::string WeakPackageFunction(const std::string& call) {
  return "package p;\n  class C;\n  endclass\n  class D extends C;\n  endclass"
         "\n  class U;\n  endclass\n  function automatic void act(\n"
         "      weak_reference #(C) wr, C c, D d, U u);\n    longint id;\n   "
         " " +
         call + "\n  endfunction\nendpackage\nmodule m;\nendmodule\n";
}

std::string WeakPackageTask(const std::string& call) {
  return "package p;\n  class C;\n  endclass\n  task automatic act(C c);\n"
         "    weak_reference #(C) wr;\n    longint id;\n    " +
         call + "\n  endtask\nendpackage\nmodule m;\nendmodule\n";
}

std::vector<std::string> InEveryScope(const std::string& call) {
  return {WeakModule(call), WeakMethod(call), WeakPackageFunction(call)};
}

void ExpectReport(const std::string& src, std::string_view at,
                  std::string_view message, std::string_view subclause) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, LineHolding(src, at),
                            subclause))
      << src;
}

void ExpectReports(const std::vector<std::string>& sources, std::string_view at,
                   std::string_view message, std::string_view subclause) {
  for (const auto& src : sources) ExpectReport(src, at, message, subclause);
}

TEST(WeakReferenceStdPackageElaborator, ClearTakesNoActual) {
  EXPECT_TRUE(ElabOk(WeakModule("wr.clear();")));
  ExpectReport(WeakModule("wr.clear(1);"), "wr.clear",
               "method 'clear' of class 'weak_reference' takes at most 0 "
               "arguments; 1 given",
               "G.7");
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_ClearTakesNoActualInAClassOrAPackage) {
  for (const auto& src :
       {WeakMethod("wr.clear();"), WeakPackageFunction("wr.clear();")}) {
    EXPECT_TRUE(ElabOk(src)) << src;
  }
  ExpectReports(
      {WeakMethod("wr.clear(1);"), WeakPackageFunction("wr.clear(1);")},
      "wr.clear",
      "method 'clear' of class 'weak_reference' takes at most 0 "
      "arguments; 1 given",
      "G.7");
}

TEST(WeakReferenceStdPackageElaborator, DISABLED_ClearIsNoOperand) {
  for (const std::string kUse : {"id = wr.clear();", "if (wr.clear()) ;",
                                 "begin automatic int i = wr.clear(); end"}) {
    ExpectReports(InEveryScope(kUse), "wr.clear",
                  "void function 'clear' used as expression operand", "13.4.1");
  }
}

TEST(WeakReferenceStdPackageElaborator, AConstructionTakesOneReferent) {
  EXPECT_TRUE(ElabOk(WeakModule("wr = new(c); wr = new(d); wr = new(null);")));
  ExpectReport(WeakModule("wr = new(c, c);"), "new(c, c)",
               "constructor of class 'weak_reference' takes at most 1 "
               "argument; 2 given",
               "G.7");
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_AReferentOfAnotherTypeIsRejected) {
  for (const std::string kCall : {"new(u)", "new(5)", "new(\"s\")"}) {
    ExpectReports(InEveryScope("wr = " + kCall + ";"), kCall,
                  "assignment compatible", "13.5");
  }
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_ReferentsAreCountedInAClassAndAPackage) {
  for (const auto& src :
       {WeakMethod("wr = new(c);"), WeakPackageFunction("wr = new(c);"),
        WeakPackageTask("wr = new(c);")}) {
    EXPECT_TRUE(ElabOk(src)) << src;
  }
  ExpectReports({WeakMethod("wr = new;"), WeakPackageFunction("wr = new;"),
                 WeakPackageTask("wr = new;")},
                "wr = new",
                "constructor of class 'weak_reference' takes at least 1 "
                "argument; 0 given",
                "G.7");
  ExpectReports(
      {WeakMethod("wr = new(c, c);"), WeakPackageTask("wr = new(c, c);")},
      "new(c, c)",
      "constructor of class 'weak_reference' takes at most 1 "
      "argument; 2 given",
      "G.7");
}

TEST(WeakReferenceStdPackageElaborator, ACastTakesTheResultOfGet) {
  for (const auto& src : InEveryScope("c = wr.get(); $cast(d, wr.get());")) {
    EXPECT_TRUE(ElabOk(src)) << src;
  }
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_TheResultOfGetIsNoHandleOfAnotherClass) {
  for (const std::string kUse : {"u = wr.get();", "d = wr.get();"}) {
    ExpectReports(InEveryScope(kUse), kUse,
                  "class handle assignment requires assignment compatible "
                  "types",
                  "8.4");
  }
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_GetTakesNoActualInAClassOrAPackage) {
  for (const std::string kUse : {"void'(wr.get(c));", "c = wr.get(c);"}) {
    ExpectReports({WeakMethod(kUse), WeakPackageFunction(kUse)}, "wr.get",
                  "method 'get' of class 'weak_reference' takes at most 0 "
                  "arguments; 1 given",
                  "G.7");
  }
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_AMethodOutsideThePrototypeIsRejectedInAClassAndAPackage) {
  ExpectReports({WeakMethod("wr.drop();"), WeakPackageFunction("wr.drop();"),
                 WeakPackageTask("wr.drop();")},
                "wr.drop", "class 'weak_reference' declares no method 'drop'",
                "G.7");
}

std::vector<std::string> DeclarationsOf(const std::string& type) {
  return {
      "class C;\nendclass\nmodule m;\n  " + type + " w;\nendmodule\n",
      "class C;\nendclass\nmodule m;\n  initial begin\n    " + type +
          " w;\n  end\nendmodule\n",
      "class C;\nendclass\nclass H;\n  " + type +
          " w;\nendclass\nmodule m;\nendmodule\n",
      "class C;\nendclass\nmodule m;\n  function void act(\n    " + type +
          " w);\n  endfunction\nendmodule\n",
      "class C;\nendclass\ntypedef " + type + " wt;\nmodule m;\nendmodule\n"};
}

TEST(WeakReferenceStdPackageElaborator,
     ADeclarationGivesItsTypeParameterAClass) {
  for (const std::string kType :
       {"weak_reference #(C)", "std::weak_reference #(C)",
        "weak_reference #(.T(C))"}) {
    for (const auto& src : DeclarationsOf(kType)) {
      EXPECT_TRUE(ElabOk(src)) << src;
    }
  }
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_ADeclarationWithoutParameterListIsRejected) {
  for (const std::string kType : {"weak_reference", "std::weak_reference"}) {
    ExpectReports(DeclarationsOf(kType), kType,
                  "parameterized class 'weak_reference' has no default "
                  "specialization",
                  "8.25");
  }
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_ADeclarationWithAnEmptyParameterListIsRejected) {
  for (const std::string kType :
       {"weak_reference #()", "std::weak_reference #()"}) {
    ExpectReports(DeclarationsOf(kType), kType,
                  "specialization of parameterized class 'weak_reference' "
                  "gives no value to parameter 'T'",
                  "8.25");
  }
}

TEST(WeakReferenceStdPackageElaborator, GetIdTakesAHandleOfTheParameterClass) {
  for (const std::string kActual : {"c", "d", "null"}) {
    for (const auto& src :
         InEveryScope("id = weak_reference#(C)::get_id(" + kActual + ");")) {
      EXPECT_TRUE(ElabOk(src)) << src;
    }
  }
}

TEST(WeakReferenceStdPackageElaborator, DISABLED_GetIdTakesOneActual) {
  ExpectReports(InEveryScope("id = weak_reference#(C)::get_id();"), "::get_id",
                "method 'get_id' of class 'weak_reference' takes at least 1 "
                "argument; 0 given",
                "G.7");
  ExpectReports(InEveryScope("id = weak_reference#(C)::get_id(c, c);"),
                "::get_id",
                "method 'get_id' of class 'weak_reference' takes at most 1 "
                "argument; 2 given",
                "G.7");
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_GetIdOfAnotherClassesHandleIsRejected) {
  ExpectReports(InEveryScope("id = weak_reference#(C)::get_id(u);"), "::get_id",
                "assignment compatible", "13.5");
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_OnlyGetIdIsCalledThroughTheClassScope) {
  for (const std::string kMethod : {"get", "clear"}) {
    ExpectReports(
        InEveryScope("weak_reference#(C)::" + kMethod + "();"), "::" + kMethod,
        "cannot reach non-static member '" + kMethod + "' through", "8.23");
  }
}

TEST(WeakReferenceStdPackageElaborator, AClassExtendsASpecialization) {
  EXPECT_TRUE(
      ElabOk("class C;\nendclass\n"
             "class W extends weak_reference#(C);\n"
             "  function new(C o);\n"
             "    super.new(o);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  W w = new(c);\n"
             "  initial begin\n"
             "    c = w.get();\n"
             "    w.clear();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(WeakReferenceStdPackageElaborator, ActualsAreBoundToTheirFormalsNames) {
  for (const std::string kCall :
       {"wr = new(.referent(c));",
        "id = weak_reference#(C)::get_id(.obj(c));"}) {
    for (const auto& src : InEveryScope(kCall)) {
      EXPECT_TRUE(ElabOk(src)) << src;
    }
  }
  EXPECT_TRUE(ElabOk(WeakModule(
      "begin static weak_reference #(C) own = new(.referent(c)); end")));
}

TEST(WeakReferenceStdPackageElaborator,
     DISABLED_ActualsBoundToOtherNamesAreRejected) {
  ExpectReports(InEveryScope("wr = new(.obj(c));"), ".obj",
                "no parameter 'obj' in", "G.7");
  ExpectReport(
      WeakModule("begin static weak_reference #(C) own = new(.obj(c)); end"),
      ".obj", "no parameter 'obj' in", "G.7");
  ExpectReports(InEveryScope("id = weak_reference#(C)::get_id(.referent(c));"),
                ".referent", "no parameter 'referent' in", "G.7");
}

}  // namespace
