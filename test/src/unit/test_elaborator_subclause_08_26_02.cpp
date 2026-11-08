#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassInheritance, InterfaceExtendsInterface) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B extends A;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, InterfaceImplementsInterfaceError) {
  ElabFixture f;
  ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B implements A;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "shall not use 'implements'",
                            4, "8.26.2"));
}

TEST(InterfaceClassImplements, InterfaceImplementsClassError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "endclass\n"
      "interface class IC implements Base;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "shall not use 'implements'",
                            3, "8.26.2"));
}

TEST(InterfaceClassImplements, InterfaceImplementsVirtualClassError) {
  ElabFixture f;
  ElabOk(
      "virtual class VBase;\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "interface class IC implements VBase;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "shall not use 'implements'",
                            4, "8.26.2"));
}

TEST(InterfaceClassInheritance, InterfaceExtendsClassError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "endclass\n"
      "interface class IC extends Base;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend non-interface class", 3, "8.26.2"));
}

TEST(ExtendsVsImplementsRestrictions, ClassExtendsInterfaceClassError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C extends IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend interface class", 4, "8.26.2"));
}

TEST(ExtendsAndImplements, ClassExtendsBaseImplementsInterface) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class Base;\n"
             "endclass\n"
             "class Child extends Base implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, SingleInterfaceImplementationOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  pure virtual function void funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  virtual function void funcC();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, ImplementsThroughAPackageIsThePackagesClass) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  interface class I; pure virtual function void g(); endclass\n"
             "endpackage\n"
             "module m;\n"
             "  interface class I; pure virtual function void f(); endclass\n"
             "  class C implements p::I;\n"
             "    virtual function void g(); endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements,
     ImplementsThroughAPackageNeedsThePackagesMethod) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  interface class I; pure virtual function void g(); endclass\n"
      "endpackage\n"
      "module m;\n"
      "  interface class I; pure virtual function void f(); endclass\n"
      "  class C implements p::I;\n"
      "    virtual function void f(); endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method 'g'", 6,
                            "8.26"));
}

TEST(InterfaceClassImplements, ClassImplementsMultipleInterfaces) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "class C implements A, B;\n"
             "  virtual function void fa();\n"
             "  endfunction\n"
             "  virtual function void fb();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, InheritedMethodSatisfiesInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcBase();\n"
             "  pure virtual function bit funcExt();\n"
             "endclass\n"
             "class BaseClass;\n"
             "  virtual function bit funcBase();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class ExtClass extends BaseClass implements IntfClass;\n"
             "  virtual function bit funcExt();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassExtends, MultipleBaseInterfaceClasses) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "interface class GetImp;\n"
             "  pure virtual function void get();\n"
             "endclass\n"
             "interface class PutGetIntf extends PutImp, GetImp;\n"
             "  pure virtual function void both();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, NonVirtualMethodDoesNotSatisfyInterface) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.26"));
}

TEST(InterfaceClassInheritance, InterfaceExtendsVirtualClassError) {
  ElabFixture f;
  ElabOk(
      "virtual class VBase;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "interface class IC extends VBase;\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend non-interface class", 4, "8.26.2"));
}

TEST(ExtendsVsImplementsRestrictions, VirtualClassExtendsInterfaceClassError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "virtual class VC extends IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend interface class", 4, "8.26.2"));
}

TEST(ExtendsVsImplementsRestrictions, ClassImplementsNonInterfaceError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "endclass\n"
      "class C implements Base;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot implement non-interface class", 3,
                            "8.26.2"));
}

TEST(InterfaceClassImplements, VirtualClassImplementsInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "virtual class VC implements IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ExtendsVsImplementsRestrictions, ClassImplementsVirtualClassError) {
  ElabFixture f;
  ElabOk(
      "virtual class VBase;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements VBase;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot implement non-interface class", 4,
                            "8.26.2"));
}

TEST(ExtendsVsImplementsRestrictions,
     ImplementsNonInterfaceReportsOnlyTheImplementsRule) {
  ElabFixture f;
  ElabOk(
      "virtual class VBase;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements VBase;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  bool claimed_unimplemented = false;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("does not implement pure virtual method") !=
        std::string::npos) {
      claimed_unimplemented = true;
    }
  }
  EXPECT_FALSE(claimed_unimplemented);
}

TEST(ExtendsVsImplementsRestrictions, VirtualClassImplementsNonInterfaceError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "endclass\n"
      "virtual class VC implements Base;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot implement non-interface class", 3,
                            "8.26.2"));
}

TEST(InterfaceClassImplements, InheritedNonVirtualFromBaseDoesNotSatisfy) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void f();\n"
      "endclass\n"
      "class BaseClass;\n"
      "  function void f();\n"
      "  endfunction\n"
      "endclass\n"
      "class ExtClass extends BaseClass implements IC;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 8,
                            "8.26"));
}

TEST(InterfaceClassImplements,
     OwnVirtualOverrideHidesNonVirtualBaseAndSatisfies) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "class BaseClass;\n"
             "  function void f();\n"
             "  endfunction\n"
             "endclass\n"
             "class ExtClass extends BaseClass implements IC;\n"
             "  virtual function void f();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
