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

// §8.26.7: a virtual class that implements an interface class but neither
// implements the prototype nor re-declares it as pure virtual is illegal.
TEST(InterfaceClassPartialImplementation,
     VirtualClassNeitherImplNorRedeclarePureError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.7: re-declaring every prototype with the pure qualifier (and providing
// no implementation) discharges the obligation for a virtual class.
TEST(InterfaceClassPartialImplementation, VirtualClassRedeclaresAllPureOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.7: implementing one prototype but leaving another neither implemented
// nor re-declared pure is illegal even though the class is virtual.
TEST(InterfaceClassPartialImplementation,
     VirtualClassPartialLeavesPrototypeUnaddressedError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.7: the prototype obligation may be discharged by a virtual method
// implementation inherited from a base class (parent §8.26 "define or
// inherit"), so no re-declaration is needed in the implementing virtual class
// itself.
TEST(InterfaceClassPartialImplementation,
     VirtualClassInheritedImplDischargesObligationOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "class Base;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "virtual class ClassA extends Base implements IntfClass;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.7: the obligation may also be discharged by a pure virtual prototype
// inherited from a base class — inheriting a pure prototype counts the same as
// re-declaring one in the implementing virtual class itself.
TEST(InterfaceClassPartialImplementation,
     VirtualClassInheritsPureBasePrototypeOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "virtual class Base;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "virtual class ClassA extends Base implements IntfClass;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.7: implementing an interface class that extends another interface class
// carries the obligation for the inherited prototypes too; addressing every
// prototype (own and inherited) is legal.
TEST(InterfaceClassPartialImplementation,
     VirtualClassImplementsExtendedInterfaceAddressesAllOk) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "interface class IB extends IA;\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IB;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.7: a prototype inherited by the implemented interface through `extends`
// that is left neither implemented nor re-declared pure is illegal, just like a
// directly declared one.
TEST(InterfaceClassPartialImplementation,
     VirtualClassImplementsExtendedInterfaceMissingInheritedError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "interface class IB extends IA;\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IB;\n"
             "  pure virtual function bit funcB();\n"
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
