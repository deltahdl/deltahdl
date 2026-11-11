#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakReferenceDeclOk) {
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

TEST(ClassConstraintElaboration, WeakReferenceAsMemberOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "class holder;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassTypeError) {
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

TEST(ClassConstraintElaboration, WeakReferenceAsFunctionArgOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  function void f(weak_reference #(my_obj) wr);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassMemberError) {
  ElabFixture f;
  ElabOk(
      "class holder;\n"
      "  weak_reference #(int) wr;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassFunctionArgError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function void f(weak_reference #(int) wr);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceModuleItemDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceModuleItemNonClassError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  weak_reference #(int) wr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceForwardTypedefClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class my_obj;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) weak_obj;\n"
             "  end\n"
             "endmodule\n"
             "class my_obj;\n"
             "  int x;\n"
             "endclass\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceTypedefAliasOfClassOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "typedef my_obj my_alias;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_alias) wr;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceTypedefNonClassError) {
  ElabFixture f;
  ElabOk(
      "typedef enum {A, B} col_t;\n"
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(col_t) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 4, "8.30.1"));
}

void ExpectNonClassWeakRefIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  logic ok;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "weak_reference needs a class type as its type parameter",
                    LineHolding(src, "weak_reference #(int) wr;"), "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassInAnAssertionPassStmt) {
  ExpectNonClassWeakRefIn("assert (ok) begin weak_reference #(int) wr; end");
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassInAnAssertionFailStmt) {
  ExpectNonClassWeakRefIn(
      "assert (ok) else begin weak_reference #(int) wr; end");
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassInARandcaseItem) {
  ExpectNonClassWeakRefIn(
      "randcase 1: begin weak_reference #(int) wr; end endcase");
}

TEST(ClassConstraintElaboration,
     WeakReferenceNonClassInARandsequenceCodeBlock) {
  ExpectNonClassWeakRefIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { begin weak_reference #(int) wr; end };\n"
      "      endsequence\n"
      "    end");
}

TEST(ClassConstraintElaboration,
     WeakReferenceNonClassInARandsequenceWeightCodeBlock) {
  ExpectNonClassWeakRefIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { begin weak_reference #(int) wr; end };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

TEST(ClassConstraintElaboration, WeakReferenceStdScopedIsTheBuiltinClass) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  std::weak_reference#(my_obj) wref1;\n"
             "  initial begin\n"
             "    std::weak_reference#(my_obj) wref2;\n"
             "  end\n"
             "endmodule\n"));
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  std::weak_reference#(int) wref1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, ModuleClassPropertyTypeArgumentIsChecked) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  class C;\n"
      "    weak_reference #(int) w;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 3, "8.30.1"));
}

TEST(ClassConstraintElaboration,
     WeakReferenceEveryNonClassTypeParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { int a; } ps_t;\n"
      "typedef struct { int a; } us_t;\n"
      "typedef int ua_t [2];\n"
      "typedef int q_t [$];\n"
      "interface ifc; endinterface\n"
      "module m;\n"
      "  weak_reference #(real) w1;\n"
      "  weak_reference #(string) w2;\n"
      "  weak_reference #(chandle) w3;\n"
      "  weak_reference #(event) w4;\n"
      "  weak_reference #(logic [7:0]) w5;\n"
      "  weak_reference #(ps_t) w6;\n"
      "  weak_reference #(us_t) w7;\n"
      "  weak_reference #(ua_t) w8;\n"
      "  weak_reference #(q_t) w9;\n"
      "  weak_reference #(virtual ifc) w10;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {7, 8, 9, 10, 11, 12, 13, 14, 15, 16}) {
    EXPECT_TRUE(ReportedError(
        diags, "weak_reference needs a class type as its type parameter", kLine,
        "8.30.1"))
        << kLine;
  }
}

TEST(ClassConstraintElaboration,
     WeakReferenceSpecializationInterfaceClassAndBuiltInParametersAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C #(int N = 1); int x = N; endclass\n"
      "typedef C #(4) c4_t;\n"
      "interface class I; pure virtual function int g(); endclass\n"
      "class K implements I; virtual function int g(); return 3; endfunction "
      "endclass\n"
      "class D; int x = 7; endclass\n"
      "module m;\n"
      "  weak_reference #(C #(4)) w1;\n"
      "  weak_reference #(c4_t) w2;\n"
      "  weak_reference #(I) w3;\n"
      "  weak_reference #(weak_reference #(D)) w4;\n"
      "  C #(4) c;\n"
      "  K k;\n"
      "  D d;\n"
      "  weak_reference #(D) wd;\n"
      "  int r1, r2, r3, r4;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    w1 = new(c);\n"
      "    w2 = new(c);\n"
      "    k = new;\n"
      "    w3 = new(k);\n"
      "    d = new;\n"
      "    wd = new(d);\n"
      "    w4 = new(wd);\n"
      "    r1 = w1.get().x;\n"
      "    r2 = w2.get().x;\n"
      "    r3 = w3.get().g();\n"
      "    r4 = (w4.get() == wd);\n"
      "    $display(\"%0d %0d %0d %0d\", r1, r2, r3, r4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassConstraintElaboration,
     WeakReferenceTypeParameterBoundToANonClassIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class H #(type P = int); weak_reference #(P) w; endclass\n"
      "module m;\n"
      "  H #(int) b;\n"
      "  H c;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "weak_reference needs a class type as its type parameter", 2,
      "8.30.1"));
}

TEST(ClassConstraintElaboration,
     DISABLED_WeakReferenceTypeParameterBoundToAClassIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class H #(type P = C); weak_reference #(P) w; endclass\n"
      "module m;\n"
      "  H #(C) a;\n"
      "  H c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassConstraintElaboration,
     WeakReferenceNonClassPropertyAndFormalAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  weak_reference #(real) p;\n"
      "  function void f(weak_reference #(string) a);\n"
      "    weak_reference #(event) l;\n"
      "  endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  function void g(weak_reference #(real) a);\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  task t(weak_reference #(chandle) a);\n"
      "    weak_reference #(logic) l;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {2, 3, 12}) {
    EXPECT_TRUE(ReportedError(
        diags, "weak_reference needs a class type as its type parameter", kLine,
        "8.30.1"))
        << kLine;
  }
}

TEST(ClassConstraintElaboration,
     DISABLED_WeakReferenceNonClassSubroutineLocalOrPackageFormalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  function void f();\n"
      "    weak_reference #(event) l;\n"
      "  endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  function void g(weak_reference #(real) a);\n"
      "  endfunction\n"
      "  function void h();\n"
      "    weak_reference #(real) l;\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  task t();\n"
      "    weak_reference #(logic) l;\n"
      "  endtask\n"
      "  function void u();\n"
      "    weak_reference #(string) l;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {3, 7, 10, 15, 18}) {
    EXPECT_TRUE(ReportedError(
        diags, "weak_reference needs a class type as its type parameter", kLine,
        "8.30.1"))
        << kLine;
  }
}

TEST(ClassConstraintElaboration,
     UserWeakReferenceClassWithoutGetIsReportedAsNamingNoMember) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "  weak_reference #(int) w = new(5);\n"
      "  int r;\n"
      "  initial r = w.get();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "class 'weak_reference' has no member named 'get'", 5, "8.6"));
}

TEST(ClassConstraintElaboration,
     ModuleWithoutAUserClassKeepsTheBuiltInWeakReference) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x = 7; endclass\n"
      "module other;\n"
      "  C h;\n"
      "  weak_reference #(C) b;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    b = new(h);\n"
      "  end\n"
      "endmodule\n"
      "module m;\n"
      "  other o ();\n"
      "  class weak_reference #(type T = int); T v; function new(T a); v = a; "
      "endfunction endclass\n"
      "  weak_reference #(int) w = new(8);\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {4, 7}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
