

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassAllowedContent, NoConstraintsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, ConstraintBlockError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "  constraint c { }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, CovergroupError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "  covergroup cg; endgroup\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, ConstraintBlockInExtendedInterfaceError) {
  EXPECT_FALSE(
      ElabOk("interface class Base;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "interface class Derived extends Base;\n"
             "  constraint c { }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, CovergroupInExtendedInterfaceError) {
  EXPECT_FALSE(
      ElabOk("interface class Base;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "interface class Derived extends Base;\n"
             "  covergroup cg; endgroup\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize, RandomizeOnInterfaceHandleOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj = new;\n"
             "    IC iref = obj;\n"
             "    void'(iref.randomize());\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize,
     RandomizeWithInlineConstraintOnInterfaceHandleOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj = new;\n"
             "    IC iref = obj;\n"
             "    void'(iref.randomize() with { });\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize, RandModeOnInterfaceHandleError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj = new;\n"
             "    IC iref = obj;\n"
             "    iref.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize, ConstraintModeOnInterfaceHandleError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj = new;\n"
             "    IC iref = obj;\n"
             "    iref.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize, OverridePreRandomizeInImplementor) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  int count;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "  function void pre_randomize();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize, OverridePostRandomizeInImplementor) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  int count;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "  function void post_randomize();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     BuiltinRandomizeMethodsAcrossInterfacesNoConflict) {
  // §8.26.9 special case: even when more than one implemented interface class
  // carries pre_randomize/post_randomize, those names shall not be treated as
  // an interface method name conflict. Declaring both in two distinct
  // interfaces and implementing both routes the names through the interface
  // method-conflict resolution, which exempts them rather than flagging the
  // collision an ordinary same-named method from two interfaces would draw.
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "class C implements A, B;\n"
             "  virtual function void fa(); endfunction\n"
             "  virtual function void fb(); endfunction\n"
             "  virtual function void pre_randomize(); endfunction\n"
             "  virtual function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     PrePostRandomizeNoConflictMultipleInterfaces) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class C;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "class D implements A, B, C;\n"
             "  virtual function void fa(); endfunction\n"
             "  virtual function void fb(); endfunction\n"
             "  virtual function void fc(); endfunction\n"
             "  function void pre_randomize(); endfunction\n"
             "  function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
