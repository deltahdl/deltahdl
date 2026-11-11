#include <gtest/gtest.h>

#include <initializer_list>

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

TEST(InterfaceClassMethodConflict, UnrelatedSpecializationsConflictError) {
  ElabFixture f;
  ElabOk(
      "interface class ia #(type T = logic);\n"
      "  pure virtual function void fn(T val);\n"
      "endclass\n"
      "interface class ib #(type T = logic);\n"
      "  pure virtual function void fn(T val);\n"
      "endclass\n"
      "interface class ic extends ia#(bit), ib#(string);\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method name conflict for 'fn' in 'ic'", 7,
                            "8.26.6.1"));
}

TEST(InterfaceClassMethodConflictElaboration,
     OneImplementationResolvesOnlyCompatiblePrototypes) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IntfBase1; pure virtual function bit funcBase(); "
      "endclass\n"
      "interface class IntfBase2; pure virtual function bit funcBase(); "
      "endclass\n"
      "virtual class ClassBase; pure virtual function bit funcBase(); "
      "endclass\n"
      "class ClassExt extends ClassBase implements IntfBase1, IntfBase2;\n"
      "  virtual function bit funcBase(); return 0; endfunction\n"
      "endclass\n"
      "interface class IntfBaseA; pure virtual function bit funcBase(); "
      "endclass\n"
      "interface class IntfBaseB; pure virtual function string funcBase(); "
      "endclass\n"
      "class ClassA implements IntfBaseA, IntfBaseB;\n"
      "  virtual function bit funcBase(); return 0; endfunction\n"
      "endclass\n"
      "interface class IAB extends IntfBaseA, IntfBaseB;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class I12 extends IntfBase1, IntfBase2;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class I12n extends IntfBase1, IntfBase2;\n"
      "endclass\n"
      "class BV; virtual function int funcBase(); return 0; endfunction "
      "endclass\n"
      "class CBV extends BV implements IntfBase1;\n"
      "  virtual function bit funcBase(); return 0; endfunction\n"
      "endclass\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {9}) {
    EXPECT_TRUE(ReportedError(diags,
                              "method name conflict for 'funcBase' in 'ClassA'",
                              kLine, "8.26.6.1"))
        << kLine;
  }
  for (const int kLine : {12}) {
    EXPECT_TRUE(ReportedError(diags,
                              "method name conflict for 'funcBase' in 'IAB'",
                              kLine, "8.26.6.1"))
        << kLine;
  }
  for (const int kLine : {22}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override has mismatched return type", kLine,
        "8.20"))
        << kLine;
  }
  for (const int kLine : {4, 15}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

const char* const kTypeParameterPrototypeSrc =
    "interface class IntfD #(type T1 = logic);\n"
    "  typedef T1 [1:0] T2;\n"
    "  pure virtual function T2 funcD();\n"
    "endclass : IntfD\n"
    "class ClassB implements IntfD #(bit);\n"
    "  virtual function bit [1:0] funcD(); return 2'b10; endfunction\n"
    "endclass : ClassB\n"
    "class ClassL implements IntfD;\n"
    "  virtual function logic [1:0] funcD(); return 2'b1x; endfunction\n"
    "endclass\n"
    "class ClassW implements IntfD #(bit);\n"
    "  virtual function bit [2:0] funcD(); return 0; endfunction\n"
    "endclass\n"
    "interface class IT #(type T1 = logic);\n"
    "  typedef T1 T3;\n"
    "  pure virtual function T1 g1();\n"
    "  pure virtual function T3 g3();\n"
    "  pure virtual function void p(T1 a);\n"
    "endclass\n"
    "class CB implements IT #(bit);\n"
    "  virtual function bit g1(); return 1; endfunction\n"
    "  virtual function bit g3(); return 1; endfunction\n"
    "  virtual function void p(bit a); endfunction\n"
    "endclass\n"
    "interface class PutImp #(type PUT_T = logic); pure virtual function void "
    "put(PUT_T a); endclass\n"
    "class CD implements PutImp;\n"
    "  virtual function void put(logic a); endfunction\n"
    "endclass\n";

TEST(InterfaceClassMethodConflictElaboration,
     ImplementationWiderThanAParameterTypedefIsReported) {
  ElabFixture f;
  ElaborateSrc(kTypeParameterPrototypeSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {12}) {
    EXPECT_TRUE(ReportedError(
        diags, "does not match signature of pure virtual method 'funcD'", kLine,
        "8.26.6.1"))
        << kLine;
  }
  for (const int kLine : {21, 23}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(InterfaceClassMethodConflictElaboration,
     DISABLED_ImplementationMatchingATypeParameterTypedefOrDefaultIsAccepted) {
  ElabFixture f;
  ElaborateSrc(kTypeParameterPrototypeSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {6, 9, 22, 27}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
