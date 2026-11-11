#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassScopeResolutionAccess, NestedClassHasTheContainingClassesAccess) {
  ElabFixture f;
  ElaborateSrc(
      "class Outer;\n"
      "  int outerProp;\n"
      "  local int outerLocalProp;\n"
      "  protected int outerProtProp;\n"
      "  static int outerStaticProp;\n"
      "  static local int outerLocalStaticProp;\n"
      "  parameter int P = 7;\n"
      "  localparam int LP = 9;\n"
      "  local function int lf(); return 3; endfunction\n"
      "  protected function int pf(); return 4; endfunction\n"
      "  static local function int slf(); return 5; endfunction\n"
      "  class Inner;\n"
      "    int ip;\n"
      "    function void innerMethod(Outer h);\n"
      "      outerStaticProp = 1;\n"
      "      outerLocalStaticProp = 2;\n"
      "      h.outerProp = 3;\n"
      "      h.outerLocalProp = 4;\n"
      "      h.outerProtProp = 5;\n"
      "      ip = h.lf() + h.pf();\n"
      "      ip = slf();\n"
      "      ip = P + LP;\n"
      "    endfunction\n"
      "    function void bad();\n"
      "      outerProp = 0;\n"
      "    endfunction\n"
      "    class Deep;\n"
      "      function void d(); outerLocalStaticProp = 6; endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endclass\n"
      "class Other;\n"
      "  function void o(Outer h);\n"
      "    h.outerLocalProp = 4;\n"
      "    h.outerProtProp = 5;\n"
      "    void'(h.lf());\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {34, 36}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot access local member from outside its class", kLine,
        "8.18"))
        << kLine;
  }
  for (const int kLine : {35}) {
    EXPECT_TRUE(ReportedError(
        diags,
        "cannot access protected member from outside its class hierarchy",
        kLine, "8.18"))
        << kLine;
  }
  for (const int kLine : {25}) {
    EXPECT_TRUE(
        ReportedError(diags,
                      "non-static property 'outerProp' of the enclosing class "
                      "'Outer' cannot be accessed unqualified",
                      kLine, "8.23"))
        << kLine;
  }
  for (const int kLine : {15, 16, 17, 18, 19, 20, 21, 22, 28}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(ClassScopeResolutionAccess,
     DISABLED_ThisInANestedClassNamesNoMemberOfTheContainingClass) {
  ElabFixture f;
  ElaborateSrc(
      "class Outer;\n"
      "  int outerProp;\n"
      "  class Inner;\n"
      "    function void bad();\n"
      "      this.outerProp = 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "class 'Inner' has no member named 'outerProp'", 5, "8.11"));
}

TEST(ClassScopeResolutionAccess, SuperclassMembersThroughTheBaseScope) {
  ElabFixture f;
  ElaborateSrc(
      "class Base;\n"
      "  static int pub;\n"
      "  protected static int prot;\n"
      "  local static int loc;\n"
      "  protected static function int pf(); return 1; endfunction\n"
      "  local static function int lf(); return 2; endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int a(); return Base::pub + Base::prot; endfunction\n"
      "  function int b(); return Base::loc; endfunction\n"
      "  function int c(); return Base::pf(); endfunction\n"
      "  function int d(); return Base::lf(); endfunction\n"
      "  static function int e(); return Base::prot; endfunction\n"
      "  static function int g(); return Base::loc; endfunction\n"
      "  function void w(); Base::prot = 1; endfunction\n"
      "  function void x(); Base::loc = 1; endfunction\n"
      "endclass\n"
      "class G extends Derived;\n"
      "  function int a(); return Base::prot; endfunction\n"
      "  function int b(); return Base::loc; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = Base::pub;\n"
      "    v = Base::prot;\n"
      "    v = Base::pf();\n"
      "    v = Derived::prot;\n"
      "    Base::prot = 2;\n"
      "    Base::pub = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {10, 12, 14, 16, 20}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot access local member from outside its class", kLine,
        "8.18"))
        << kLine;
  }
  for (const int kLine : {26, 27, 28, 29}) {
    EXPECT_TRUE(ReportedError(
        diags,
        "cannot access protected member from outside its class hierarchy",
        kLine, "8.18"))
        << kLine;
  }
  for (const int kLine : {9, 11, 13, 15, 19, 25, 30}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 9u);
}

const char* const kNonClassPrefixSrc =
    "class C; static int y; typedef int y_t; static function int f(); return "
    "1; endfunction endclass\n"
    "typedef int T;\n"
    "typedef struct { int y; } S;\n"
    "typedef enum {A, B} E;\n"
    "typedef C TC;\n"
    "typedef TC T2;\n"
    "function int uf();\n"
    "  T::y_t a;\n"
    "  TC::y_t b;\n"
    "  int r;\n"
    "  r = T::y + S::y + E::A + T::f();\n"
    "  r = TC::y + T2::y + TC::f();\n"
    "  return r;\n"
    "endfunction\n"
    "package p;\n"
    "  typedef int PT;\n"
    "  typedef C PC;\n"
    "  PT::y_t a;\n"
    "  PC::y_t b;\n"
    "  function int pf();\n"
    "    int r;\n"
    "    r = PT::y + PT::f();\n"
    "    r = PC::y + PC::f();\n"
    "    return r;\n"
    "  endfunction\n"
    "endpackage\n"
    "class K;\n"
    "  function int kf();\n"
    "    T::y_t a;\n"
    "    TC::y_t b;\n"
    "    int r;\n"
    "    r = S::y + E::A + T::f();\n"
    "    r = T2::y + TC::f();\n"
    "    return r;\n"
    "  endfunction\n"
    "endclass\n"
    "module top;\n"
    "  int x, v;\n"
    "  T::y_t z1;\n"
    "  S::y_t z2;\n"
    "  TC::y_t z3;\n"
    "  initial begin\n"
    "    x = T::y;\n"
    "    x = S::y;\n"
    "    x = E::A;\n"
    "    x = T::f();\n"
    "    x = TC::y + T2::y + TC::f();\n"
    "    x = v::y;\n"
    "    x = top::y;\n"
    "  end\n"
    "endmodule\n";

TEST(ClassScopeResolutionAccess, VariableOrModulePrefixAndClassTypedefPrefix) {
  ElabFixture f;
  ElaborateSrc(kNonClassPrefixSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {48, 49}) {
    EXPECT_TRUE(ReportedError(diags, "reference to unresolved package or scope",
                              kLine, "26.3"))
        << kLine;
  }
  for (const int kLine : {9, 12, 19, 23, 30, 33, 41, 47}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ClassScopeResolutionAccess, DISABLED_NonClassTypedefPrefixIsReported) {
  ElabFixture f;
  ElaborateSrc(kNonClassPrefixSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {8, 11, 18, 22, 29, 32, 39, 40, 43, 44, 45, 46}) {
    EXPECT_TRUE(ReportedError(diags, "is not a class", kLine, "8.23")) << kLine;
  }
}

const char* const kForwardPrefixSrc =
    "typedef class C;\n"
    "C::T u1;\n"
    "typedef C::T ut;\n"
    "package p;\n"
    "  typedef class PC;\n"
    "  PC::T a;\n"
    "  typedef PC::T pt;\n"
    "  class PC; typedef int T; static int n; endclass\n"
    "  PC::T b;\n"
    "endpackage\n"
    "class K;\n"
    "  typedef class KC;\n"
    "  KC::T m;\n"
    "  typedef KC::T kt;\n"
    "  class KC; typedef int T; endclass\n"
    "  KC::T m2;\n"
    "endclass\n"
    "module top;\n"
    "  typedef class D;\n"
    "  D::T x1;\n"
    "  typedef D::T dt;\n"
    "  var type(D::T) v;\n"
    "  localparam type U = D::T;\n"
    "  int y1, y2, y3;\n"
    "  assign y2 = D::n;\n"
    "  int y4 = D::n;\n"
    "  initial y1 = D::n;\n"
    "  class D; typedef int T; static int n; endclass\n"
    "  D::T x2;\n"
    "  initial y3 = D::n;\n"
    "endmodule\n"
    "class C; typedef int T; endclass\n"
    "C::T u2;\n";

TEST(ClassScopeResolutionAccess, ForwardPrefixInAllowedPlacesIsAccepted) {
  ElabFixture f;
  ElaborateSrc(kForwardPrefixSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine :
       {3, 7, 9, 14, 16, 21, 22, 23, 25, 26, 27, 29, 30, 34}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ClassScopeResolutionAccess,
     DISABLED_TypeThroughAnIncompleteForwardPrefixIsRestricted) {
  ElabFixture f;
  ElaborateSrc(kForwardPrefixSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {2, 6, 13, 20}) {
    EXPECT_TRUE(ReportedError(
        diags, "may prefix the class scope resolution operator only within",
        kLine, "8.23"))
        << kLine;
  }
}

const char* const kInterfaceTypedefPrefixSrc =
    "interface ifc;\n"
    "  class IC; typedef int T; static int n = 4; endclass\n"
    "  typedef IC ict;\n"
    "endinterface\n"
    "module m(ifc i);\n"
    "  typedef i.ict lt;\n"
    "  lt::T a;\n"
    "  typedef lt::T t2;\n"
    "  int y;\n"
    "  initial y = lt::n;\n"
    "endmodule\n"
    "module top;\n"
    "  ifc i();\n"
    "  m u(i);\n"
    "endmodule\n";

TEST(ClassScopeResolutionAccess, TypeThroughAnInterfaceTypedefIsRestricted) {
  ElabFixture f;
  ElaborateSrc(kInterfaceTypedefPrefixSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {7}) {
    EXPECT_TRUE(ReportedError(
        diags, "may prefix the class scope resolution operator only within",
        kLine, "8.23"))
        << kLine;
  }
  for (const int kLine : {8}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ClassScopeResolutionAccess,
     DISABLED_ValueThroughARestrictedPrefixIsAccepted) {
  ElabFixture f;
  ElaborateSrc(kInterfaceTypedefPrefixSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {10}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
  ElabFixture g;
  ElaborateSrc(
      "module top;\n"
      "  typedef class N;\n"
      "  int y;\n"
      "  initial y = N::n;\n"
      "endmodule\n",
      g);
  EXPECT_FALSE(ErrorOnLine(g.diag.Diagnostics(), 4));
  EXPECT_TRUE(ReportedError(g.diag.Diagnostics(),
                            "forward typedef 'N' is never resolved", 2,
                            "6.18"));
}

}  // namespace
