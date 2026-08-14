#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassTypeUsageRestrictions, InterfaceDeclaredBeforeUseOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions, ParameterizedInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC #(type T = int);\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions, ClassImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "class Fifo #(type T = PutImp) implements T;\n"
      "  virtual function void put();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 4, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     VirtualClassImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "virtual class Fifo #(type T = PutImp) implements T;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 4, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsConcreteAndTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "class C #(type T = B) implements A, T;\n"
      "  virtual function void fa();\n"
      "  endfunction\n"
      "  virtual function void fb();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 7, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions, InterfaceExtendsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "interface class Fifo #(type T = PutImp) extends T;\n"
      "  pure virtual function void get();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not extend type parameter", 4, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsConcreteAndTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "interface class C #(type T = B) extends A, T;\n"
      "  pure virtual function void fc();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not extend type parameter", 7, "8.26.4"));
}

// §8.1 lets a class be declared wherever a data declaration may appear, so the
// three below write theirs inside a module. Every other case in this file
// declares at compilation-unit scope, which is the convenient placement and the
// one that cannot tell a rule enforced everywhere from a rule enforced at the
// top of a file: a validator reading only the compilation unit's own classes
// passes all of them and reaches none of these.
TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAModuleImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAModuleImplementsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  typedef interface class IC;\n"
      "  class C implements IC;\n"
      "    virtual function void foo();\n"
      "    endfunction\n"
      "  endclass\n"
      "  interface class IC;\n"
      "    pure virtual function void foo();\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement forward typedef", 3,
                            "8.26.4"));
}

// The control the two above need: the same placement with the interface
// declared ahead of the class that implements it is ordinary and stays legal,
// so neither error can be passing because a class inside a module is rejected
// out of hand.
TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAModuleImplementsInterfaceDeclaredAheadOfItOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  interface class IC;\n"
             "    pure virtual function void foo();\n"
             "  endclass\n"
             "  class C implements IC;\n"
             "    virtual function void foo();\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

// §8.1 admits the same declaration inside a package, an interface and a
// program, and a class may enclose a class in turn. Each of the four below
// varies only the scope the classes are written in, because that placement is
// the one thing a validator can be reached by or miss: the rule they all state
// is the rule the module-scope case above states.
TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAPackageImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAnInterfaceImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface intf;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAProgramImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "program prog;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endprogram\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassNestedInAClassImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "class Outer;\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement type parameter", 5, "8.26.4"));
}

// The control the four above need: the same nesting with an ordinary
// `implements` of a named interface class stays legal, so none of them can be
// passing because a class written outside the compilation unit, or inside
// another class, is rejected out of hand.
TEST(InterfaceClassTypeUsageRestrictions,
     ClassNestedInAClassImplementsNamedInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Outer;\n"
             "  class Fifo implements PutImp;\n"
             "    virtual function void put();\n"
             "    endfunction\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions, ClassImplementsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IC;\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement forward typedef", 2,
                            "8.26.4"));
}

// The literal §8.26.4 example: the forward typedef is referenced through a
// parameterized `#(...)` argument list (from §6.20.3) while the class is
// declared ahead of the real interface declaration. The forward-typedef rule
// must still fire when the reference carries type-parameter arguments.
TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsParameterizedForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IntfD;\n"
      "class ClassB implements IntfD #(bit);\n"
      "  virtual function void funcD();\n"
      "  endfunction\n"
      "endclass\n"
      "interface class IntfD #(type T1 = logic);\n"
      "  pure virtual function void funcD();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement forward typedef", 2,
                            "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     VirtualClassImplementsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IC;\n"
      "virtual class VC implements IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not implement forward typedef", 2,
                            "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions, InterfaceExtendsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IC;\n"
      "interface class IC2 extends IC;\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not extend forward typedef", 2, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsUndeclaredInterfaceError) {
  ElabFixture f;
  ElabOk(
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "' must be declared before it is implemented by '",
                            1, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsUndeclaredInterfaceError) {
  ElabFixture f;
  ElabOk(
      "interface class IC2 extends IC;\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "' must be declared before it is extended by '", 1,
                            "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsInterfaceWithTypeParamArgOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp #(type T = logic);\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo #(type T = int) implements PutImp #(T);\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsInterfaceWithTypeParamArgOk) {
  EXPECT_TRUE(
      ElabOk("interface class A #(type T = logic);\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B #(type T = bit) extends A #(T);\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ForwardTypedefThenDeclThenImplementsOk) {
  EXPECT_TRUE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions, ForwardTypedefThenDeclThenExtendsOk) {
  EXPECT_TRUE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "interface class IC2 extends IC;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
