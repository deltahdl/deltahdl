#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AbstractClassElaboration, AbstractClassOk) {
  EXPECT_TRUE(
      ElabOk("virtual class Base;\n"
             "  pure virtual function void display();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, ConcreteOverridesAllPureVirtuals) {
  EXPECT_TRUE(
      ElabOk("virtual class Shape;\n"
             "  pure virtual function int area();\n"
             "endclass\n"
             "class Circle extends Shape;\n"
             "  virtual function int area(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Circle c;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, OverrideWithoutVirtualKeywordImplementsPure) {
  EXPECT_TRUE(
      ElabOk("virtual class Shape;\n"
             "  pure virtual function int area();\n"
             "  pure virtual task draw();\n"
             "endclass\n"
             "class Circle extends Shape;\n"
             "  function int area(); return 3; endfunction\n"
             "  task draw(); endtask\n"
             "endclass\n"
             "module m;\n"
             "  Circle c;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, NonAbstractMissingPureVirtualError) {
  ElabFixture f;
  ElabOk(
      "virtual class Shape;\n"
      "  pure virtual function int area();\n"
      "endclass\n"
      "class Circle extends Shape;\n"
      "endclass\n"
      "module m;\n"
      "  Circle c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.21"));
}

TEST(AbstractClassElaboration, AbstractExtendsAbstractOk) {
  EXPECT_TRUE(
      ElabOk("virtual class Shape;\n"
             "  pure virtual function int area();\n"
             "endclass\n"
             "virtual class Shape2D extends Shape;\n"
             "  pure virtual function int perimeter();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, NonAbstractMissingInheritedPureVirtualError) {
  ElabFixture f;
  ElabOk(
      "virtual class Shape;\n"
      "  pure virtual function int area();\n"
      "endclass\n"
      "virtual class Shape2D extends Shape;\n"
      "  pure virtual function int perimeter();\n"
      "endclass\n"
      "class Rect extends Shape2D;\n"
      "  virtual function int area(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Rect r;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 7,
                            "8.21"));
}

TEST(AbstractClassElaboration, ConcreteImplementsAllDeepPureVirtuals) {
  EXPECT_TRUE(
      ElabOk("virtual class Shape;\n"
             "  pure virtual function int area();\n"
             "endclass\n"
             "virtual class Shape2D extends Shape;\n"
             "  pure virtual function int perimeter();\n"
             "endclass\n"
             "class Rect extends Shape2D;\n"
             "  virtual function int area(); endfunction\n"
             "  virtual function int perimeter(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Rect r;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, ConcreteExtendedToAbstractOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function void foo(); endfunction\n"
             "endclass\n"
             "virtual class AbstractDerived extends Base;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, EmptyBodyMethodNotPureVirtual) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function int compute(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Base b;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, AbstractClassNoPureVirtualsOk) {
  EXPECT_TRUE(
      ElabOk("virtual class Base;\n"
             "  function void foo(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, PureVirtualTaskMustBeOverridden) {
  ElabFixture f;
  ElabOk(
      "virtual class Base;\n"
      "  pure virtual task run();\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.21"));
}

TEST(AbstractClassElaboration, PureVirtualTaskOverriddenOk) {
  EXPECT_TRUE(
      ElabOk("virtual class Base;\n"
             "  pure virtual task run();\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  virtual task run(); endtask\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration, AbstractClassAddsNewPureVirtuals) {
  EXPECT_TRUE(
      ElabOk("class Concrete;\n"
             "  function void foo(); endfunction\n"
             "endclass\n"
             "virtual class AbstractDerived extends Concrete;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "class ConcreteFinal extends AbstractDerived;\n"
             "  virtual function void bar(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  ConcreteFinal c;\n"
             "endmodule\n"));
}

TEST(AbstractClassElaboration,
     AbstractClassAddsNewPureVirtualsNotOverriddenError) {
  ElabFixture f;
  ElabOk(
      "class Concrete;\n"
      "  function void foo(); endfunction\n"
      "endclass\n"
      "virtual class AbstractDerived extends Concrete;\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "class ConcreteFinal extends AbstractDerived;\n"
      "endclass\n"
      "module m;\n"
      "  ConcreteFinal c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 7,
                            "8.21"));
}

TEST(AbstractClassElaboration, BaseLessNonAbstractPureVirtualIsAnError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  pure virtual function void f();\n"
      "endclass\n"
      "package p;\n"
      "  virtual class A; pure virtual function void g(); endclass\n"
      "  class D extends A; endclass\n"
      "endpackage\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-abstract class 'C' does not implement pure "
                            "virtual method 'f'",
                            1, "8.21"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-abstract class 'D' does not implement pure "
                            "virtual method 'g'",
                            6, "8.21"));
}

TEST(AbstractClassElaboration, ConstructingAnAbstractClassIsAnError) {
  ElabFixture f;
  ElabOk(
      "virtual class B; endclass\n"
      "class D extends B; endclass\n"
      "module m;\n"
      "  B b0 = new;\n"
      "  B b1;\n"
      "  initial begin\n"
      "    B b2 = B::new;\n"
      "    if (0) b1 = new;\n"
      "    b1 = B::new;\n"
      "    b1 = D::new;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const int kLine : {4, 7, 8, 9}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "cannot construct object of abstract class 'B'",
                              kLine, "8.21"))
        << kLine;
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "cannot construct", 10, "8.21"));
}

const char* const kConstructionSrc =
    "virtual class A;\n"
    "  pure virtual function int f();\n"
    "endclass\n"
    "class D extends A; function int f(); return 1; endfunction endclass\n"
    "package pk;\n"
    "  virtual class PA; endclass\n"
    "  class PD extends PA; endclass\n"
    "  PA pa = new;\n"
    "  PA pb = PD::new;\n"
    "  function automatic PA mk(); PA x = new; return x; endfunction\n"
    "endpackage\n"
    "function automatic A ua(); A x; x = new; return x; endfunction\n"
    "function automatic A ub(); A x; x = D::new; return x; endfunction\n"
    "program pr;\n"
    "  A a;\n"
    "  initial a = new;\n"
    "  initial a = D::new;\n"
    "endprogram\n"
    "interface ifc;\n"
    "  A a = new;\n"
    "  D d = new;\n"
    "endinterface\n"
    "class Q;\n"
    "  A a;\n"
    "  function void g(); a = new; endfunction\n"
    "  function void h(); a = A::new; endfunction\n"
    "endclass\n"
    "module m;\n"
    "  A a;\n"
    "  for (genvar i = 0; i < 1; i++) begin : gl\n"
    "    initial a = new;\n"
    "  end\n"
    "  initial begin\n"
    "    a = A::new;\n"
    "    a = D::new;\n"
    "  end\n"
    "  pr p(); ifc i();\n"
    "endmodule\n";

TEST(AbstractClassElaboration, ConstructingAnAbstractClassIsReportedInPlace) {
  ElabFixture f;
  ElabOk(kConstructionSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {12, 16, 20, 25, 26, 34}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot construct object of abstract class", kLine, "8.21"))
        << kLine;
  }
  for (const int kLine : {9, 13, 17, 21, 35}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(AbstractClassElaboration,
     DISABLED_ConstructingAnAbstractClassInAPackageOrGenerateIsReported) {
  ElabFixture f;
  ElabOk(kConstructionSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {8, 10, 31}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot construct object of abstract class", kLine, "8.21"))
        << kLine;
  }
}

const char* const kPureVirtualSrc =
    "package pk;\n"
    "  class N1; pure virtual function void f(); endclass\n"
    "  virtual class PA; pure virtual task t(); endclass\n"
    "  class PD extends PA; endclass\n"
    "  class PE extends PA; task t(); endtask endclass\n"
    "endpackage\n"
    "class B0; virtual function int v(); return 1; endfunction endclass\n"
    "virtual class B1 extends B0; pure virtual function int v(); endclass\n"
    "class B2 extends B1; endclass\n"
    "class B3 extends B1; function int v(); return 3; endfunction endclass\n"
    "virtual class B4 extends B1; endclass\n"
    "program pr;\n"
    "  class N2; pure virtual task t(); endclass\n"
    "  virtual class A; pure virtual function int f(); endclass\n"
    "  class D extends A; endclass\n"
    "endprogram\n"
    "interface ifc;\n"
    "  virtual class A; pure virtual function int f(); pure virtual function "
    "int g(); endclass\n"
    "  class D extends A; function int f(); return 1; endfunction endclass\n"
    "  class E extends A; function int f(); return 1; endfunction function int "
    "g(); return 2; endfunction endclass\n"
    "endinterface\n"
    "module m;\n"
    "  class N3; pure virtual function int f(); endclass\n"
    "  virtual class A; pure virtual function int f(); endclass\n"
    "  if (1) begin : gb\n"
    "    class D extends A; endclass\n"
    "    class N4; pure virtual function int f(); endclass\n"
    "  end\n"
    "  pr p(); ifc i();\n"
    "endmodule\n";

TEST(AbstractClassElaboration, PureVirtualRulesHoldInEveryPlace) {
  ElabFixture f;
  ElabOk(kPureVirtualSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {2, 4, 9, 13, 15, 19, 23, 27}) {
    EXPECT_TRUE(ReportedError(diags, "does not implement pure virtual method",
                              kLine, "8.21"))
        << kLine;
  }
  for (const int kLine : {5, 10, 11, 20}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(AbstractClassElaboration,
     DISABLED_AGenerateBlockClassExtendingAnAbstractClassMustOverride) {
  ElabFixture f;
  ElabOk(kPureVirtualSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "non-abstract class 'D' does not implement pure virtual method 'f'", 26,
      "8.21"));
}

}  // namespace
