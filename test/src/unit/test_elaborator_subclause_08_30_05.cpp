#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakRefGetIdStaticCallOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj o;\n"
             "    longint id;\n"
             "    o = new();\n"
             "    id = weak_reference#(obj)::get_id(o);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefGetIdWithNullOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    longint id;\n"
             "    id = weak_reference#(obj)::get_id(null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefGetIdInExpressionOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj o;\n"
             "    o = new();\n"
             "    if (weak_reference#(obj)::get_id(o) != 0)\n"
             "      $display(\"has id\");\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefGetIdDerivedHandleArgOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "class ex_obj extends obj;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    ex_obj my_obj;\n"
             "    longint id;\n"
             "    my_obj = new();\n"
             "    id = weak_reference#(obj)::get_id(my_obj);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration,
     DISABLED_WeakRefGetIdOfAnotherClassIsReported) {
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
    for (const int kLine : {18}) {
      EXPECT_TRUE(ReportedError(diags, "assignment compatible", kLine, "13.5"))
          << kLine;
    }
    for (const int kLine : {22}) {
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
    for (const int kLine : {16, 35}) {
      EXPECT_TRUE(ReportedError(diags, "assignment compatible", kLine, "13.5"))
          << kLine;
    }
    for (const int kLine : {20, 39}) {
      EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
    }
  }
}

}  // namespace
