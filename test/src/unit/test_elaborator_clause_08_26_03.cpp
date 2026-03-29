#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Requirement 1: Parameters and typedefs inherited by extending interface
// classes via extends.

TEST(InterfaceClassTypeAccess, TypedefInheritedByExtendingInterface) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA;\n"
             "  typedef int my_t;\n"
             "  pure virtual function void funcA();\n"
             "endclass\n"
             "interface class IntfB extends IntfA;\n"
             "  pure virtual function void funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ParamInheritedByExtendingInterface) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA;\n"
             "  parameter int SIZE = 64;\n"
             "  pure virtual function void funcA();\n"
             "endclass\n"
             "interface class IntfB extends IntfA;\n"
             "  pure virtual function void funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, TypedefUsedInExtendingInterfaceMethod) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA #(type T1 = logic);\n"
             "  typedef T1[1:0] T2;\n"
             "  pure virtual function T2 funcA();\n"
             "endclass\n"
             "interface class IntfB #(type T = bit) extends IntfA #(T);\n"
             "  pure virtual function T2 funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ChainedTypedefInheritanceThroughExtends) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  typedef int my_t;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class IB extends IA;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class IC extends IB;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Requirement 2: Parameters and typedefs NOT inherited by implementing classes
// via implements.

TEST(InterfaceClassTypeAccess, TypedefNotInheritedByImplementingClass) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  virtual function IntfC::t1_t funcC();\n"
             "    return (IntfC::ONE);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ParamNotInheritedByImplementingClass) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  parameter int SIZE = 64;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = IC::SIZE;\n"
             "endmodule\n"));
}

// Requirement 4: Access via :: scope resolution operator.

TEST(InterfaceClassTypeAccess, ScopeResolutionAccessToTypedef) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IntfC::t1_t x;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ScopeResolutionAccessToParam) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  parameter int WIDTH = 8;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = IC::WIDTH;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ScopeResolutionAccessToEnumValue) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = IntfC::ONE;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ScopeResolutionOnParameterizedInterfaceClass) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA #(type T1 = logic);\n"
             "  typedef T1[1:0] T2;\n"
             "  pure virtual function T2 funcA();\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IntfA#(bit)::T2 val;\n"
             "  end\n"
             "endmodule\n"));
}

// Requirement 3: All parameters and typedefs in interface classes are static.

TEST(InterfaceClassTypeAccess, ParamsAreStaticAccessibleWithoutInstance) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  parameter int SIZE = 64;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = IC::SIZE;\n"
             "endmodule\n"));
}

}  // namespace
