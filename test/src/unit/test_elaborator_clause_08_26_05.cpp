#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Req 1: Assign object handle to interface class variable.

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

TEST(InterfaceClassCastingAndRefAssignment, AssignImplHandleToMultipleIfaceVarsOk) {
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

// Req 4: Interface class objects shall not be constructed.

TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassDeclElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
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

}  // namespace
