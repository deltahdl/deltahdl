#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(InterfaceClassPartialImplementation,
     VirtualClassNeitherImplNorRedeclarePureError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfClass;\n"
      "  pure virtual function bit funcA();\n"
      "endclass\n"
      "virtual class ClassA implements IntfClass;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "neither implements nor re-declares as pure virtual the method", 4,
      "8.26.7"));
}

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

TEST(InterfaceClassPartialImplementation,
     VirtualClassPartialLeavesPrototypeUnaddressedError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfClass;\n"
      "  pure virtual function bit funcA();\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "virtual class ClassA implements IntfClass;\n"
      "  virtual function bit funcA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "neither implements nor re-declares as pure virtual the method", 5,
      "8.26.7"));
}

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

TEST(InterfaceClassPartialImplementation,
     VirtualClassImplementsExtendedInterfaceMissingInheritedError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  pure virtual function bit funcA();\n"
      "endclass\n"
      "interface class IB extends IA;\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "virtual class ClassA implements IB;\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "neither implements nor re-declares as pure virtual the method", 7,
      "8.26.7"));
}

TEST(InterfaceClassPartialImplementation,
     ConcreteClassFailsToCompletePartialError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfClass;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 11,
                            "8.26"));
}

TEST(InterfaceClassPartialImplementation,
     ConcreteDirectImplementsMissingMethodError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfClass;\n"
      "  pure virtual function bit funcA();\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "class ClassA implements IntfClass;\n"
      "  virtual function bit funcA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 5,
                            "8.26"));
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
  ElabFixture f;
  ElabOk(
      "interface class IntfClass;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 13,
                            "8.26"));
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

TEST(InterfaceClassPartialImplementation,
     VirtualClassInsideAModuleLeavingAPrototypeUnaddressedError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class IntfClass;\n"
      "    pure virtual function bit funcA();\n"
      "    pure virtual function bit funcB();\n"
      "  endclass\n"
      "  virtual class ClassA implements IntfClass;\n"
      "    virtual function bit funcA();\n"
      "      return 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "neither implements nor re-declares as pure virtual the method", 6,
      "8.26.7"));
}

TEST(InterfaceClassPartialImplementation, VirtualClassInsideAModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  interface class IntfClass;\n"
             "    pure virtual function bit funcA();\n"
             "    pure virtual function bit funcB();\n"
             "  endclass\n"
             "  virtual class ClassA implements IntfClass;\n"
             "    virtual function bit funcA();\n"
             "      return 1;\n"
             "    endfunction\n"
             "    pure virtual function bit funcB();\n"
             "  endclass\n"
             "endmodule\n"));
}

}  // namespace
