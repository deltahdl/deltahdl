#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassStructElaboration, HandleCastOntoEveryNonClassTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; C nx; function C me(); return this; endfunction endclass\n"
      "typedef bit [7:0] byte_t;\n"
      "typedef enum {E0, E1} e_t;\n"
      "typedef struct packed { int a; } s_t;\n"
      "module m;\n"
      "  C h;\n"
      "  C arr [2];\n"
      "  int i;\n"
      "  real r;\n"
      "  string s;\n"
      "  byte_t b;\n"
      "  e_t e;\n"
      "  s_t st;\n"
      "  logic [63:0] w;\n"
      "  initial begin\n"
      "    i = int'(h);\n"
      "    w = longint'(h);\n"
      "    w = logic'(h);\n"
      "    r = real'(h);\n"
      "    s = string'(h);\n"
      "    b = byte_t'(h);\n"
      "    e = e_t'(h);\n"
      "    st = s_t'(h);\n"
      "    w = 64'(h);\n"
      "    w = signed'(h);\n"
      "    w = unsigned'(h);\n"
      "    i = int'(h.nx);\n"
      "    i = int'(arr[0]);\n"
      "    i = int'(h.me());\n"
      "    i = int'(null);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {16, 17, 18, 19, 20, 21, 22, 23, 25, 26}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot cast class object handle to a non-class type", kLine,
        "8.4"))
        << kLine;
  }
  EXPECT_TRUE(ReportedError(
      diags, "a size cast works only on an integral value", 24, "6.24.1"));
}

TEST(ClassStructElaboration, HandleCastInEveryScopeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "  function int g(C o); return int'(o); endfunction\n"
      "endclass\n"
      "function automatic int uf(C o);\n"
      "  return int'(o);\n"
      "endfunction\n"
      "interface ifc;\n"
      "  C h;\n"
      "  int i;\n"
      "  initial i = int'(h);\n"
      "endinterface\n"
      "program prg;\n"
      "  C h;\n"
      "  int i;\n"
      "  initial i = int'(h);\n"
      "endprogram\n"
      "module m;\n"
      "  C h;\n"
      "  int i;\n"
      "  task automatic t(C o);\n"
      "    i = int'(o);\n"
      "  endtask\n"
      "  always_comb i = int'(h);\n"
      "  ifc u ();\n"
      "  prg p ();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {3, 6, 11, 16, 22, 24}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot cast class object handle to a non-class type", kLine,
        "8.4"))
        << kLine;
  }
}

TEST(ClassStructElaboration,
     HandleAssignmentAndDynamicCastBetweenClassesAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class D; int a; endclass\n"
      "class E extends D; endclass\n"
      "module m;\n"
      "  D d, d2;\n"
      "  E e;\n"
      "  int i;\n"
      "  initial begin\n"
      "    e = new;\n"
      "    d = e;\n"
      "    d2 = d;\n"
      "    i = $cast(e, d);\n"
      "    i = (d == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassStructElaboration,
     DISABLED_CastOfThisAMemberAnElementOrAResultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  C nx;\n"
      "  function int f(); return int'(this); endfunction\n"
      "  function C me(); return this; endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  class P; endclass\n"
      "  function automatic int pf(P o);\n"
      "    return int'(o);\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  C h;\n"
      "  C arr [2];\n"
      "  int i;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    i = int'(h.nx);\n"
      "    i = int'(arr[0]);\n"
      "    i = int'(h.me());\n"
      "  end\n"
      "  if (1) begin : g\n"
      "    C gh;\n"
      "    int gi;\n"
      "    initial gi = int'(gh);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {3, 9, 18, 19, 20, 25}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot cast class object handle to a non-class type", kLine,
        "8.4"))
        << kLine;
  }
}

}  // namespace
