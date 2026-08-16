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

// Every report in this file stands at the offending class declaration, which is
// the location ValidateInterfaceClassInheritance and
// ValidateRegularClassInheritance in
// src/elaborator/elaborator_validate_class_overrides.cpp pass as
// cls->range.start.
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

// An interface class is barred from the 'implements' mechanism entirely: it may
// not implement a regular class (nor a virtual class) any more than it may
// implement another interface class. Inheritance for an interface class is
// exclusively through 'extends' targeting interface classes.
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

// The "or virtual class" arm of the same prohibition: an interface class naming
// a virtual class after 'implements' is rejected just as a regular-class target
// is. The bar is on an interface class using 'implements' at all, so the target
// being virtual rather than plain does not change the outcome.
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

// The rule that rejects this source is §8.26's requirement that an implementing
// class supply every pure virtual method, not the §8.26.2 extends/implements
// restriction the rest of this file covers: a non-virtual method is not an
// implementation, so CheckInterfaceMethods in
// src/elaborator/elaborator_validate_class_inheritance.cpp finds none and
// reports under §8.26.
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

// §8.26.2: the 'implements' target must be an interface class. A *virtual*
// class is still a class, not an interface class, so naming one after
// 'implements' is rejected exactly as a regular class would be — this covers
// the "or virtual class" input form of that prohibition, which the plain-class
// case above does not exercise.
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

// §8.26.2: naming a non-interface class after 'implements' breaks that
// subclause and nothing else, so the report above is the only one the source
// draws. §8.26 poses the obligation to provide an implementation for a pure
// virtual method only where an interface class is implemented (printed page 209
// of ~/LRM.pdf), and VBase is a virtual class, so a report saying C fails to
// implement 'foo' "from interface 'VBase'" states something false about the
// source and names a clause the source does not break.
//
// The assertion is about what was not reported, which ReportedError cannot say:
// it answers whether some recorded error matches, and passes whether or not a
// second one stands beside it. So the case above holds that the §8.26.2 report
// is present and this one holds that the §8.26 report is absent; a fix that
// suppressed both would satisfy only one of the two.
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

// §8.26.2: the same prohibition applies when the implementing subject is itself
// a virtual class — a virtual class may implement interface classes but not a
// (non-interface) regular class.
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

// Like NonVirtualMethodDoesNotSatisfyInterface, the report here is §8.26's
// unimplemented-prototype rule rather than the §8.26.2 restriction: the
// inherited method is not virtual, so it does not discharge the prototype.
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

// A subclass that declares its own virtual method of the same name as a
// non-virtual base method hides that base method, and the override is what
// satisfies the implemented interface's pure virtual requirement.
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
