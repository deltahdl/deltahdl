#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakRefNewWithReferentOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj strong_obj;\n"
             "    weak_reference #(obj) wr;\n"
             "    strong_obj = new();\n"
             "    wr = new(strong_obj);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefNewWithNullOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(obj) wr;\n"
             "    wr = new(null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefTwoInstancesSameReferentOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj strong_obj;\n"
             "    weak_reference #(obj) wref1, wref2;\n"
             "    strong_obj = new();\n"
             "    wref1 = new(strong_obj);\n"
             "    wref2 = new(strong_obj);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefNewArityIsReportedInAModule) {
  ElabFixture f;
  ElaborateSrc(
      "class B; int x = 7; endclass\n"
      "class D extends B; endclass\n"
      "class U; endclass\n"
      "module m;\n"
      "  B b;\n"
      "  D d, z;\n"
      "  U u;\n"
      "  weak_reference #(B) w;\n"
      "  initial begin\n"
      "    b = new;\n"
      "    d = new;\n"
      "    u = new;\n"
      "    w = new(u);\n"
      "    w = new(5);\n"
      "    w = new(\"s\");\n"
      "    w = new();\n"
      "    w = new(b, b);\n"
      "    w = new(b);\n"
      "    w = new(d);\n"
      "    w = new(null);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, "takes at least 1 argument; 0 given", 16, "G.7"));
  EXPECT_TRUE(
      ReportedError(diags, "takes at most 1 argument; 2 given", 17, "G.7"));
}

TEST(ClassConstraintElaboration,
     DISABLED_WeakRefNewArgumentOfAnotherTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class B; int x = 7; endclass\n"
      "class D extends B; endclass\n"
      "class U; endclass\n"
      "module m;\n"
      "  B b;\n"
      "  D d, z;\n"
      "  U u;\n"
      "  weak_reference #(B) w;\n"
      "  initial begin\n"
      "    b = new;\n"
      "    d = new;\n"
      "    u = new;\n"
      "    w = new(u);\n"
      "    w = new(5);\n"
      "    w = new(\"s\");\n"
      "    w = new();\n"
      "    w = new(b, b);\n"
      "    w = new(b);\n"
      "    w = new(d);\n"
      "    w = new(null);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {13, 14, 15}) {
    EXPECT_TRUE(ReportedError(diags, "assignment compatible", kLine, "13.5"))
        << kLine;
  }
  for (const int kLine : {18, 19, 20}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ClassConstraintElaboration,
     DISABLED_WeakRefNewInAClassMethodOrPackageFunctionIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "class B; int x = 7; endclass\n"
      "class D extends B; endclass\n"
      "class U; endclass\n"
      "class K;\n"
      "  function void f(B b, D d, U u);\n"
      "    weak_reference #(B) w;\n"
      "    D z;\n"
      "    int i;\n"
      "    longint k;\n"
      "    w = new(u);\n"
      "    w = new(5);\n"
      "    w = new();\n"
      "    u = w.get();\n"
      "    z = w.get();\n"
      "    i = w.clear();\n"
      "    k = weak_reference #(B)::get_id(u);\n"
      "    w = new(d);\n"
      "    b = w.get();\n"
      "    w.clear();\n"
      "    k = weak_reference #(B)::get_id(d);\n"
      "  endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  class PB; endclass\n"
      "  class PU; endclass\n"
      "  function void g(PB b, PU u);\n"
      "    weak_reference #(PB) w;\n"
      "    int i;\n"
      "    longint k;\n"
      "    w = new(u);\n"
      "    w = new(5);\n"
      "    w = new();\n"
      "    u = w.get();\n"
      "    i = w.clear();\n"
      "    k = weak_reference #(PB)::get_id(u);\n"
      "    w = new(b);\n"
      "    b = w.get();\n"
      "    w.clear();\n"
      "    k = weak_reference #(PB)::get_id(b);\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {10, 11, 30, 31}) {
    EXPECT_TRUE(ReportedError(diags, "assignment compatible", kLine, "13.5"))
        << kLine;
  }
  for (const int kLine : {12, 32}) {
    EXPECT_TRUE(ReportedError(diags, "takes at least 1 argument; 0 given",
                              kLine, "G.7"))
        << kLine;
  }
  for (const int kLine : {17, 36}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
