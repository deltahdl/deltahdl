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

}  // namespace
