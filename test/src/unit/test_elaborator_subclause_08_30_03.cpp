#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakRefGetCallOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj strong_obj;\n"
             "    weak_reference #(obj) wr;\n"
             "    obj result;\n"
             "    strong_obj = new();\n"
             "    wr = new(strong_obj);\n"
             "    result = wr.get();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefGetInWaitOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(obj) wr;\n"
             "    wr = new(null);\n"
             "    wait (wr.get() == null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration,
     DISABLED_WeakRefGetResultIntoAnIncompatibleVariableIsReported) {
  {
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
        "  int i;\n"
        "  longint k;\n"
        "  initial begin\n"
        "    b = new;\n"
        "    w = new(b);\n"
        "    u = w.get();\n"
        "    z = w.get();\n"
        "    i = w.clear();\n"
        "    if (w.clear()) ;\n"
        "    k = weak_reference #(B)::get_id(u);\n"
        "    b = w.get();\n"
        "    void'($cast(z, w.get()));\n"
        "    w.clear();\n"
        "    k = weak_reference #(B)::get_id(d);\n"
        "  end\n"
        "endmodule\n",
        f);
    const auto& diags = f.diag.Diagnostics();
    for (const int kLine : {14, 15}) {
      EXPECT_TRUE(ReportedError(
          diags, "class handle assignment requires assignment compatible types",
          kLine, "8.4"))
          << kLine;
    }
    for (const int kLine : {19, 20}) {
      EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
    }
  }
  {
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
    for (const int kLine : {13, 14, 33}) {
      EXPECT_TRUE(ReportedError(
          diags, "class handle assignment requires assignment compatible types",
          kLine, "8.4"))
          << kLine;
    }
    for (const int kLine : {18, 37}) {
      EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
    }
  }
}

}  // namespace
