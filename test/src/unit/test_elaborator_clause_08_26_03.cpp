#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

// §8.26.3 elaboration case: a typedef whose definition uses the interface
// class's type parameter resolves against the specialization named on the left
// of ::, so IntfA#(bit)::T2 elaborates to bit[1:0]. The parser file for this
// subclause carries the matching claim that the syntax itself parses.
TEST(InterfaceClassTypeAccess,
     ScopeResolutionAccessToTypedefOfSpecializedInterfaceClass) {
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

// §8.26.3 negative: a typedef of an interface class is not inherited through
// 'implements'. Referencing it unqualified as a member type in the implementing
// class is the error the LRM example marks. Mirrors the standard's Example 2.
TEST(InterfaceClassTypeAccess, TypedefUnqualifiedInImplementingClassIsError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  t1_t t1_i;\n"
             "  virtual function IntfC::t1_t funcC();\n"
             "    return (IntfC::ONE);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.3 accepting path (control): the same member typed with the interface
// scope prefix resolves and is legal, so the rule keys on the unqualified form
// only.
TEST(InterfaceClassTypeAccess, TypedefQualifiedMemberInImplementingClassOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  IntfC::t1_t t1_i;\n"
             "  virtual function IntfC::t1_t funcC();\n"
             "    return (IntfC::ONE);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.3 negative, input-form: the rule is not specific to the enum typedef of
// the LRM example — a plain scalar typedef of the interface is equally not
// inherited through 'implements', so its unqualified use as a member type in
// the implementing class is likewise an error.
TEST(InterfaceClassTypeAccess,
     PlainTypedefUnqualifiedInImplementingClassIsError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfC;\n"
             "  typedef int my_t;\n"
             "  pure virtual function my_t funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  my_t m_i;\n"
             "  virtual function IntfC::my_t funcC();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.3 guard: a same-named typedef declared locally in the implementing
// class is visible without a prefix, so the unqualified use resolves to the
// local type rather than the interface's and is not flagged.
TEST(InterfaceClassTypeAccess, LocalTypedefShadowsInterfaceTypedef) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  typedef int t1_t;\n"
             "  t1_t t1_i;\n"
             "  virtual function IntfC::t1_t funcC();\n"
             "    return (IntfC::ONE);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.3 negative, method argument: the rule is about where a name resolves,
// not about which kind of declaration writes it down. A method argument typed
// with the interface's typedef spells the same unqualified name a data member
// would, and it is not inherited through 'implements' either.
TEST(InterfaceClassTypeAccess, TypedefUnqualifiedInMethodArgumentIsError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfC;\n"
             "  typedef int int_t;\n"
             "  pure virtual function void hello(int_t val);\n"
             "endclass\n"
             "class Hello implements IntfC;\n"
             "  virtual function void hello(int_t val);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.3 negative, method return type: the other position a method names a
// type in. Kept apart from the argument case so that an implementation that
// walked only the argument list would fail one of the two.
TEST(InterfaceClassTypeAccess, TypedefUnqualifiedInMethodReturnTypeIsError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfC;\n"
             "  typedef int int_t;\n"
             "  pure virtual function int_t hello();\n"
             "endclass\n"
             "class Hello implements IntfC;\n"
             "  virtual function int_t hello();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.3 accepting path (control): the same method written with the interface
// scope prefix on both its argument and its return type resolves and is legal,
// so the rule keys on the unqualified form rather than on the mention.
TEST(InterfaceClassTypeAccess, TypedefQualifiedInMethodSignatureOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef int int_t;\n"
             "  pure virtual function int_t hello(int_t val);\n"
             "endclass\n"
             "class Hello implements IntfC;\n"
             "  virtual function IntfC::int_t hello(IntfC::int_t val);\n"
             "    return val;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.3 negative, inside a module: classes declared in a module scope are
// held to the rule as classes declared at compilation-unit scope are. This is
// the shape the sv-tests case for this subclause is written in, and the scope
// is the whole of the difference between it and the case above it.
TEST(InterfaceClassTypeAccess,
     TypedefUnqualifiedInMethodArgumentInsideAModuleIsError) {
  EXPECT_FALSE(
      ElabOk("module class_tb;\n"
             "  interface class ihello;\n"
             "    typedef int int_t;\n"
             "    pure virtual function void hello(int_t val);\n"
             "  endclass\n"
             "  class Hello implements ihello;\n"
             "    virtual function void hello(int_t val);\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

// §8.26.3 guard, method argument: a typedef the implementing class declares
// itself is visible without a prefix, so an argument typed with that name
// resolves to the local type and is not flagged.
TEST(InterfaceClassTypeAccess, LocalTypedefShadowsInterfaceTypedefInArgument) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef int int_t;\n"
             "  pure virtual function void hello(int_t val);\n"
             "endclass\n"
             "class Hello implements IntfC;\n"
             "  typedef int int_t;\n"
             "  virtual function void hello(int_t val);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
