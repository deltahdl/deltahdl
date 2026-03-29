#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassAllowedContent, InterfaceClassTypeAndParamOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  typedef int my_int;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassNonPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassDataMemberError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassMultiplePureVirtualsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "  pure virtual function int bar();\n"
             "  pure virtual task do_stuff();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassImplementsInterface, ConcreteMethodSatisfiesPureVirtual) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, MissingPureVirtualImplementation) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, AllPureVirtualMethodsImplemented) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  virtual function bit funcB();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, ParameterDeclarationOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  parameter int WIDTH = 8;\n"
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

TEST(InterfaceClassAllowedContent, NestedClassError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "  class Nested;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassNestedInInterfaceClassError) {
  EXPECT_FALSE(
      ElabOk("interface class Outer;\n"
             "  pure virtual function void foo();\n"
             "  interface class Inner;\n"
             "    pure virtual function void bar();\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, SubclassInheritsInterfaceImplementation) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class B implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "class C extends B;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
