#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassPartialImplementation, VirtualClassPartialImplOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation, ConcreteClassCompletesPartialOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "class ClassB extends ClassA;\n"
             "  virtual function bit funcB();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation, VirtualClassNoImplOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation,
     ConcreteClassFailsToCompletePartialError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "class ClassB extends ClassA;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation,
     ConcreteDirectImplementsMissingMethodError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation,
     VirtualClassPartialMultipleInterfacesOk) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit fA();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function bit fB();\n"
             "endclass\n"
             "virtual class ClassA implements IA, IB;\n"
             "  virtual function bit fA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit fB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation,
     ChainedVirtualClassesCompletedByConcreteOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "  pure virtual function bit funcC();\n"
             "endclass\n"
             "virtual class V1 implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit funcB();\n"
             "  pure virtual function bit funcC();\n"
             "endclass\n"
             "virtual class V2 extends V1;\n"
             "  virtual function bit funcB();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Concrete extends V2;\n"
             "  virtual function bit funcC();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation,
     ChainedVirtualClassesStillIncompleteError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class V1 implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class V2 extends V1;\n"
             "endclass\n"
             "class Concrete extends V2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPartialImplementation, VirtualClassAllMethodsImplOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
