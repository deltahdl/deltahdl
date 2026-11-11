#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstantClassPropertyWriteForms,
     DISABLED_HandleWriteInAPackageOrUnitFunctionOrGenerateIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "  const int id;\n"
      "  int v;\n"
      "  function new(); id = 1; endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  class K; const int k = 5; int v; endclass\n"
      "  function automatic void pf(K h); h.k = 7; endfunction\n"
      "  function automatic void pg(K h); h.v = 7; endfunction\n"
      "endpackage\n"
      "function automatic void uf(C h); h.k = 7; endfunction\n"
      "function automatic void ug(C h); h.id = 7; endfunction\n"
      "function automatic void uh(C h); h.v = 7; endfunction\n"
      "module m;\n"
      "  C h = new;\n"
      "  for (genvar i = 0; i < 1; i++) begin : gl\n"
      "    initial h.k = 9;\n"
      "    initial h.v = 9;\n"
      "  end\n"
      "  if (1) begin : gb initial h.id = 9; end\n"
      "  case (1) 1: begin : gc initial h.k <= 9; end endcase\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {9, 12, 18, 22}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to global constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {13, 21}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to instance constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {10, 14, 19}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ConstantClassPropertyWriteForms, WriteFromEveryOtherPlaceIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "  const int id;\n"
      "  int v;\n"
      "  static const int sk = 3;\n"
      "  function new(); id = 1; endfunction\n"
      "  extern function void ob();\n"
      "endclass\n"
      "function void C::ob();\n"
      "  k = 6;\n"
      "  id = 2;\n"
      "  v = 1;\n"
      "endfunction\n"
      "package pk;\n"
      "  class K; const int k = 5; int v;\n"
      "    function void f(); k = 6; endfunction\n"
      "    function void g(); v = 6; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "program pr;\n"
      "  C h = new;\n"
      "  initial h.k = 8;\n"
      "  initial h.v = 8;\n"
      "endprogram\n"
      "interface ifc;\n"
      "  C h = new;\n"
      "  initial h.id = 8;\n"
      "  initial h.v = 8;\n"
      "endinterface\n"
      "checker ck(logic clk);\n"
      "  C h = new;\n"
      "  always_ff @(posedge clk) h.k <= 1;\n"
      "  always_ff @(posedge clk) h.v <= 1;\n"
      "endchecker\n"
      "module m;\n"
      "  C h = new; logic clk;\n"
      "  initial C::sk = 4;\n"
      "  initial h.k <= 2;\n"
      "  initial h.v <= 2;\n"
      "  pr p(); ifc i(); ck c1(clk);\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {10, 16, 22, 32, 37, 38}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to global constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {11, 27}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to instance constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {6, 12, 17, 23, 28, 33, 39}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ConstantClassPropertyWriteForms,
     DISABLED_IncrementAndAssignmentExpressionWritesAreReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "  const int id;\n"
      "  int v, x;\n"
      "  function new(); id++; endfunction\n"
      "  extern function void ob();\n"
      "  function void f();\n"
      "    k++;\n"
      "    --k;\n"
      "    for (int i = 0; i < 1; k++) ;\n"
      "    x = (k = 1);\n"
      "    this.k += 1;\n"
      "    id--;\n"
      "    v++; --v; x = (v = 1); this.v += 1;\n"
      "  endfunction\n"
      "endclass\n"
      "function void C::ob();\n"
      "  k++;\n"
      "  v++;\n"
      "endfunction\n"
      "class D extends C;\n"
      "  function void g();\n"
      "    ++k;\n"
      "    ++v;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h = new;\n"
      "  int y;\n"
      "  task t();\n"
      "    h.k++;\n"
      "    y = (h.k = 2);\n"
      "    h.v++;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {8, 9, 10, 11, 12, 18, 23, 31, 32}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to global constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {13}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to instance constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {5, 14, 19, 24, 33}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ConstantClassPropertyWriteForms,
     DISABLED_OutputInoutAndRefArgumentWritesAreReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "  const int id;\n"
      "  int v;\n"
      "  task o(output int a); a = 1; endtask\n"
      "  task io(inout int a); a = 1; endtask\n"
      "  task rf(ref int a); a = 1; endtask\n"
      "  task in(input int a); endtask\n"
      "  function new(); o(id); endfunction\n"
      "  task f();\n"
      "    o(k);\n"
      "    io(this.k);\n"
      "    rf(k);\n"
      "    io(id);\n"
      "    in(k);\n"
      "    o(v); io(v); rf(v);\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C h = new;\n"
      "  task t();\n"
      "    h.o(h.k);\n"
      "    h.in(h.k);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {11, 12, 13, 22}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to global constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {14}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to instance constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {9, 15, 16, 23}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ConstantClassPropertyWriteForms,
     DISABLED_SystemCallArgumentWritesAreReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "  const string s = \"ab\";\n"
      "  const int id;\n"
      "  int v, x; string t;\n"
      "  function new(); void'($cast(id, 3)); endfunction\n"
      "  function void f();\n"
      "    void'($cast(k, x));\n"
      "    $sformat(s, \"%d\", 1);\n"
      "    $swrite(s, \"%d\", 1);\n"
      "    void'($sscanf(\"7\", \"%d\", k));\n"
      "    void'($value$plusargs(\"n=%d\", k));\n"
      "    x = $random(k);\n"
      "    x = $dist_uniform(this.k, 0, 9);\n"
      "    void'($fgets(s, 1));\n"
      "    void'($cast(id, x));\n"
      "    void'($cast(v, x)); $sformat(t, \"%d\", 1); x = $random(v);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h = new;\n"
      "  task t2(); $sformat(h.s, \"%d\", 2); endtask\n"
      "  task t3(); $sformat(h.t, \"%d\", 2); endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {8, 9, 10, 11, 12, 13, 14, 15, 22}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to global constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {16}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to instance constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {6, 17, 23}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ConstantClassPropertyWriteForms,
     DISABLED_StringAndArrayMethodWritesAreReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const string s = \"ab\";\n"
      "  const int q[$] = '{3, 1};\n"
      "  const int a[2] = '{2, 1};\n"
      "  const int aa[int] = '{1: 1};\n"
      "  const int k = 5;\n"
      "  string t; int vq[$]; int va[2]; int vaa[int]; int x;\n"
      "  function void f();\n"
      "    s.putc(0, \"a\");\n"
      "    s.itoa(5);\n"
      "    q.push_back(1);\n"
      "    void'(q.pop_front());\n"
      "    q.insert(0, 1);\n"
      "    q.delete(0);\n"
      "    a.sort();\n"
      "    a.reverse();\n"
      "    a.shuffle();\n"
      "    aa.delete(1);\n"
      "    void'(vaa.first(k));\n"
      "    t.putc(0, \"a\"); t.itoa(5); vq.push_back(1); va.sort(); "
      "vaa.delete(1); void'(vaa.first(x));\n"
      "    x = s.len() + q.size() + a.sum() + aa.num();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h = new;\n"
      "  task t2(); h.q.push_back(2); endtask\n"
      "  task t3(); h.vq.push_back(2); endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 26}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to global constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {20, 21, 27}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ConstantClassPropertyWriteForms,
     DISABLED_RandomizeArgumentWritesAreReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "  rand int r;\n"
      "  int v;\n"
      "  function void f();\n"
      "    void'(randomize(k));\n"
      "    void'(std::randomize(k));\n"
      "    void'(this.randomize(k));\n"
      "    void'(randomize(v));\n"
      "    void'(std::randomize(v));\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h = new;\n"
      "  task t(); void'(h.randomize(k)); endtask\n"
      "  task u(); void'(h.randomize(v)); endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {6, 7, 8, 15}) {
    EXPECT_TRUE(
        ReportedError(diags, "assignment to global constant", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {9, 10, 16}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ConstantClassPropertyWriteForms,
     DISABLED_AWriteOfAnyFormIsTheConstructorsOneAssignment) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int a;\n"
      "  const int b;\n"
      "  const int c;\n"
      "  const int d;\n"
      "  task o(output int x); x = 1; endtask\n"
      "  function new();\n"
      "    a++;\n"
      "    a = 2;\n"
      "    b = (c = 1);\n"
      "    o(b);\n"
      "    void'($cast(d, 4));\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h = new;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {9, 11}) {
    EXPECT_TRUE(ReportedError(
        diags, "is assigned more than once in the constructor", kLine, "8.19"))
        << kLine;
  }
  for (const int kLine : {8, 10, 12}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
