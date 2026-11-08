#include <gtest/gtest.h>

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

}  // namespace
