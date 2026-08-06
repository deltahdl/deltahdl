#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassCastingAndRefAssignment, InterfaceRefAssignOk) {
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

TEST(InterfaceClassCastingAndRefAssignment, AssignImplHandleToIfaceVarOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo implements PutImp;\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo fifo_obj;\n"
             "    PutImp put_ref;\n"
             "    fifo_obj = new;\n"
             "    put_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     AssignImplHandleToMultipleIfaceVarsOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "interface class GetImp;\n"
             "  pure virtual function void get();\n"
             "endclass\n"
             "class Fifo implements PutImp, GetImp;\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "  virtual function void get();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo fifo_obj;\n"
             "    PutImp put_ref;\n"
             "    GetImp get_ref;\n"
             "    fifo_obj = new;\n"
             "    put_ref = fifo_obj;\n"
             "    get_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassNewError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IC ic;\n"
             "    ic = new;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: assigning an object handle to an interface-class variable the object
// implements is legal when written as a declaration initializer too -- the
// exact syntactic form the LRM example uses (`PutImp put_ref = fifo_obj;`),
// which is distinct from the procedural-assignment form covered above.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignImplHandleToIfaceVarDeclInitOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo implements PutImp;\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo fifo_obj = new;\n"
             "    PutImp put_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: assigning an object handle to an interface-class variable is legal
// only when the object's class implements that interface. Class C does not
// implement IC, so the handle assignment is not assignment compatible and must
// be rejected at elaboration.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignUnimplementedHandleToIfaceVarError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C c_obj;\n"
             "    IC ic_ref;\n"
             "    c_obj = new;\n"
             "    ic_ref = c_obj;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: an object of an interface class type shall not be constructed. The
// construction here is written as a block-local declaration initializer
// (`IC ic = new;`) rather than a procedural assignment, and must be rejected
// just the same.
TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassNewDeclInitError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IC ic = new;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: the interface-class construction prohibition also applies when the
// declaration initializer appears at module scope (`IC ic = new;` as a module
// item) rather than inside a procedural block.
TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewModuleScopeDeclInitError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "  IC ic = new;\n"
             "endmodule\n"));
}

// §8.26.5: the construction prohibition is specific to interface classes; a
// declaration initializer that constructs a concrete class implementing the
// interface is legal and must still elaborate. This guards the new decl-init
// check against over-rejecting ordinary class construction.
TEST(InterfaceClassCastingAndRefAssignment, ConcreteClassNewDeclInitOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C c = new;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: the object-handle-to-interface-variable assignment is legal when the
// interface class is parameterized and the object's class implements the same
// specialization -- the exact shape of the LRM's own example
// (`PutImp#(int) put_ref = fifo_obj;`). The interface class and the
// implementing class both carry a type parameter, so this exercises the
// assignment-compatibility check across parameterized types, a distinct input
// form from the non-parameterized cases above.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignParamImplHandleToParamIfaceVarOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp #(type T = logic);\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo #(type T = int) implements PutImp #(T);\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo #(int) fifo_obj;\n"
             "    PutImp #(int) put_ref;\n"
             "    fifo_obj = new;\n"
             "    put_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: a class implements an interface class when it does so through a
// superclass as well as directly. Assigning a derived-class object handle to a
// variable of an interface class implemented by the base class is legal, so the
// assignment-compatibility check must accept it -- an input form where the
// implements relationship is produced by inheritance rather than a direct
// implements clause on the object's own class.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignInheritedImplHandleToIfaceVarOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class Base implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Derived d;\n"
             "    IC ic;\n"
             "    d = new;\n"
             "    ic = d;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: the prohibition on constructing an interface-class object applies to
// a parameterized interface class the same as a plain one -- constructing a
// specialization such as `PutImp#(int)` with 'new' must still be rejected.
TEST(InterfaceClassCastingAndRefAssignment, ParamInterfaceClassNewError) {
  EXPECT_FALSE(
      ElabOk("interface class PutImp #(type T = logic);\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    PutImp #(int) p;\n"
             "    p = new;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
