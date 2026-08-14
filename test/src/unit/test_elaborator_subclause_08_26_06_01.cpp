

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodConflict, SingleImplResolvesConflict) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase1;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfBase2;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "class ClassExt implements IntfBase1, IntfBase2;\n"
             "  virtual function bit funcBase();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, ExtendsAndImplementsConflictOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IntfBase1;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class IntfBase2;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "virtual class ClassBase;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "class ClassExt extends ClassBase implements IntfBase1, IntfBase2;\n"
      "  virtual function bit funcBase();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, InterfaceExtendsMultipleWithSameMethodOk) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "endclass\n"
             "class D implements IC;\n"
             "  virtual function bit f();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The report for two interfaces disagreeing over one method name stands at the
// class that names them both, not at either interface: it is that class whose
// method set cannot be built. Every case below that pits two interfaces against
// each other therefore names the line of the implementing or extending class.
TEST(InterfaceClassMethodConflict, IncompatibleReturnTypesError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfBaseA;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class IntfBaseB;\n"
      "  pure virtual function string funcBase();\n"
      "endclass\n"
      "class ClassA implements IntfBaseA, IntfBaseB;\n"
      "  virtual function bit funcBase();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 7,
                            "8.26.6.1"));
}

TEST(InterfaceClassMethodConflict, IncompatibleArgCountError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  pure virtual function void f(int a);\n"
      "endclass\n"
      "interface class IB;\n"
      "  pure virtual function void f(int a, int b);\n"
      "endclass\n"
      "class C implements IA, IB;\n"
      "  virtual function void f(int a);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 7,
                            "8.26.6.1"));
}

TEST(InterfaceClassMethodConflict, IncompatibleArgTypesError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  pure virtual function void f(int a);\n"
      "endclass\n"
      "interface class IB;\n"
      "  pure virtual function void f(string a);\n"
      "endclass\n"
      "class C implements IA, IB;\n"
      "  virtual function void f(int a);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 7,
                            "8.26.6.1"));
}

TEST(InterfaceClassMethodConflict,
     InterfaceExtendsIncompatibleReturnTypesError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  pure virtual function bit f();\n"
      "endclass\n"
      "interface class IB;\n"
      "  pure virtual function int f();\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 7,
                            "8.26.6.1"));
}

// Nothing here pits two interfaces against each other: IA contributes the only
// interface prototype for f, and C's own f matches it. What C breaks is the
// signature of the pure virtual f it inherits from Base, so the report is
// §8.20's rule about a virtual method override and it stands at C's f rather
// than at C. §8.26.6.1's own rule about a name a class inherits from a base
// class and an interface class alike goes unreported.
TEST(InterfaceClassMethodConflict, ImplConflictsWithInheritedBaseMethodError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  pure virtual function int f();\n"
      "endclass\n"
      "virtual class Base;\n"
      "  pure virtual function bit f();\n"
      "endclass\n"
      "class C extends Base implements IA;\n"
      "  virtual function int f();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual method override has mismatched return type", 8, "8.20"));
}

TEST(InterfaceClassMethodConflict, VirtualClassPrototypeResolvesConflict) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "virtual class V implements IA, IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "class C extends V;\n"
             "  virtual function bit f();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Claim A: the single resolving "implementation" need not be declared in the
// implementing class itself; a concrete virtual method inherited from a base
// class can simultaneously satisfy the same-named pure virtuals of every
// implemented interface.
TEST(InterfaceClassMethodConflict, InheritedConcreteMethodResolvesConflict) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "class Base;\n"
             "  virtual function bit f();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base implements IA, IB;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Claim B: even when the two implemented interfaces agree on a compatible
// same-named prototype (so there is no interface-vs-interface conflict), the
// single resolving method must itself be a valid virtual method override of
// that prototype. Here the interfaces both declare `bit f()`, but the class's
// implementation returns `int`, so it is not a valid override and an error is
// required. This isolates the impl-signature check from the
// interface-vs-interface conflict check.
// The report stands at C's own f, not at C, which is what separates this case
// from the interface-versus-interface ones: the two interfaces agree, and it is
// the implementing method that does not match them.
TEST(InterfaceClassMethodConflict, ImplMustValidlyOverrideAgreeingInterfaces) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  pure virtual function bit f();\n"
      "endclass\n"
      "interface class IB;\n"
      "  pure virtual function bit f();\n"
      "endclass\n"
      "class C implements IA, IB;\n"
      "  virtual function int f();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not match signature of pure virtual method",
                            8, "8.26.6.1"));
}

// Claim A (cannot be resolved): the conflicting interface prototypes differ
// only in argument direction, so no single method can be a valid simultaneous
// implementation of both, and an error is required.
TEST(InterfaceClassMethodConflict, IncompatibleArgDirectionError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  pure virtual function void f(input int a);\n"
      "endclass\n"
      "interface class IB;\n"
      "  pure virtual function void f(output int a);\n"
      "endclass\n"
      "class C implements IA, IB;\n"
      "  virtual function void f(input int a);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 7,
                            "8.26.6.1"));
}

// §8.1 lets a class be declared inside a module, and the conflict rule has to
// reach it there. The interface classes below are named from a class in the
// same module, so a lookup confined to the compilation unit's own classes finds
// neither and the conflict goes unreported.
TEST(InterfaceClassMethodNameConflicts, ConflictInsideAModuleIsReported) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class ihello;\n"
      "    pure virtual function void hello();\n"
      "  endclass\n"
      "  interface class itest;\n"
      "    pure virtual function int hello();\n"
      "  endclass\n"
      "  class Hello implements ihello, itest;\n"
      "    virtual function void hello();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 8,
                            "8.26.6.1"));
}

// The control: the same two interfaces agreeing on the prototype conflict over
// nothing, so the class implementing both is ordinary and stays legal.
TEST(InterfaceClassMethodNameConflicts, AgreeingPrototypesInsideAModuleAreOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  interface class ihello;\n"
             "    pure virtual function void hello();\n"
             "  endclass\n"
             "  interface class itest;\n"
             "    pure virtual function void hello();\n"
             "  endclass\n"
             "  class Hello implements ihello, itest;\n"
             "    virtual function void hello();\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

// A name two modules both declare is a name this lookup must not answer for:
// resolving it to whichever module came first would hold a class against an
// interface the source never named. The class below implements an interface
// declared in its own module, and the same name stands in another module with a
// prototype it does not satisfy -- which must not be what it is judged by.
TEST(InterfaceClassMethodNameConflicts,
     ANameTwoModulesDeclareIsNotResolvedAcrossThem) {
  EXPECT_TRUE(
      ElabOk("module a;\n"
             "  interface class ihello;\n"
             "    pure virtual function void hello();\n"
             "  endclass\n"
             "endmodule\n"
             "module b;\n"
             "  interface class ihello;\n"
             "    pure virtual function void hello();\n"
             "  endclass\n"
             "  class Hello implements ihello;\n"
             "    virtual function void hello();\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

}  // namespace
