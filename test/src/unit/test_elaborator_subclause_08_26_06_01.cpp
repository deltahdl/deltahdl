#include <gtest/gtest.h>

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

}  // namespace
