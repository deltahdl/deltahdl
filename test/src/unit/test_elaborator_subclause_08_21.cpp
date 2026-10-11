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

// §8.20 (printed page 197): an override of a virtual method is virtual
// without the keyword, so a plain `function int area()` in Circle implements
// Shape's pure area() and Circle is no abstract class; counted only when
// written `virtual`, the override left area() reported as unimplemented.
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

// The report stands at the offending subclass's own declaration -- the site
// passes `cls->range.start` -- rather than at the pure virtual method it leaves
// unimplemented.
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

// §8.21: a class not declared virtual is a constructible one, so a pure
// virtual method of its own is unimplemented whether or not it extends a
// class. The rule holds over a class a package declares too.
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

// §8.21 forbids constructing an object of an abstract class directly, which is
// a rule on the source: a bare new for a handle of the class, as a module or
// block declaration's initializer or assigned in a statement that never runs,
// and a typed constructor call naming it are each reported at elaboration. A
// typed constructor call naming a concrete subclass stays legal.
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

}  // namespace
