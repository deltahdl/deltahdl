#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.21: Abstract class declaration is OK.
TEST(ElabA821, AbstractClassOk) {
  EXPECT_TRUE(
      ElabOk("virtual class Base;\n"
             "  pure virtual function void display();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.21: Concrete class overriding all pure virtuals is OK.
TEST(ElabA821, ConcreteOverridesAllPureVirtuals) {
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

// §8.21: Non-abstract class not implementing pure virtual — error.
TEST(ElabA821, NonAbstractMissingPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("virtual class Shape;\n"
             "  pure virtual function int area();\n"
             "endclass\n"
             "class Circle extends Shape;\n"
             "endclass\n"
             "module m;\n"
             "  Circle c;\n"
             "endmodule\n"));
}

// §8.21: Abstract class extending abstract — may leave pure virtuals.
TEST(ElabA821, AbstractExtendsAbstractOk) {
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

// §8.21: Non-abstract class must implement all inherited pure virtuals.
TEST(ElabA821, NonAbstractMissingInheritedPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("virtual class Shape;\n"
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
             "endmodule\n"));
}

// §8.21: :final on pure virtual method — error.
TEST(ElabA821, FinalOnPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("virtual class Base;\n"
             "  pure virtual function :final void display();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.21: Non-abstract class implementing all inherited pure virtuals — OK.
TEST(ElabA821, ConcreteImplementsAllDeepPureVirtuals) {
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

// §8.21: Any class may be extended into an abstract class.
TEST(ElabA821, ConcreteExtendedToAbstractOk) {
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

// §8.21: Method without body in non-abstract class with virtual is still
// a legal method (returns 'x) — not the same as pure virtual.
TEST(ElabA821, EmptyBodyMethodNotPureVirtual) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function int compute(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Base b;\n"
             "endmodule\n"));
}

}  // namespace
