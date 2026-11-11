#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakRefClearCallOk) {
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
             "    wr.clear();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, DISABLED_WeakRefClearUsedAsAValueIsReported) {
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
    for (const int kLine : {16, 17}) {
      EXPECT_TRUE(ReportedError(
          diags, "void function 'clear' used as expression operand", kLine,
          "13.4.1"))
          << kLine;
    }
    for (const int kLine : {21}) {
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
    for (const int kLine : {15, 34}) {
      EXPECT_TRUE(ReportedError(
          diags, "void function 'clear' used as expression operand", kLine,
          "13.4.1"))
          << kLine;
    }
    for (const int kLine : {19, 38}) {
      EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
    }
  }
}

}  // namespace
