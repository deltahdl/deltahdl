#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.20: Virtual method in base class is OK.
TEST(ElabA820, VirtualMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void display(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Base b;\n"
             "endmodule\n"));
}

// §8.20: Virtual method override in derived is OK.
TEST(ElabA820, VirtualOverrideOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void display(); endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  virtual function void display(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.20: :initial and :extends mutually exclusive — error.
TEST(ElabA820, InitialAndExtendsError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function :initial :extends void foo(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §8.20: :initial on method overriding virtual base method — error.
TEST(ElabA820, InitialOverridesVirtualError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  function :initial void f2(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

// §8.20: :extends on method not overriding a virtual — error.
TEST(ElabA820, ExtendsNoVirtualBaseError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function void f1(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function :extends void f5(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

// §8.20: Override :final method — error.
TEST(ElabA820, OverrideFinalError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function :final void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

// §8.20: :initial on non-virtual base method is OK.
TEST(ElabA820, InitialNonVirtualBaseOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function void f1(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  function :initial void f1(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

// §8.20: :extends :final combined is OK when overriding virtual.
TEST(ElabA820, ExtendsFinalOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function :extends :final void f2(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

}  // namespace
