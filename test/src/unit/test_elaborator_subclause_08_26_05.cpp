#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    IC ic;\n"
      "    ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

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
             "    static Fifo fifo_obj = new;\n"
             "    static PutImp put_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     AssignUnimplementedHandleToIfaceVarError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "class handle assignment requires assignment compatible "
                    "types",
                    11, "8.4"));
}

TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassNewDeclInitError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    static IC ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 6,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewModuleScopeDeclInitError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic = new;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 5,
                            "8.26.5"));
}

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
             "    static C c = new;\n"
             "  end\n"
             "endmodule\n"));
}

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

TEST(InterfaceClassCastingAndRefAssignment, ParamInterfaceClassNewError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp #(type T = logic);\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    PutImp #(int) p;\n"
      "    p = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    fork\n"
      "      ic = new;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 8,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    assert (1) ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    assert (1) else ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : ic = new;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 8,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { ic = new; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 8,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewDeclInitInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      static IC ic2 = new;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewDeclInitInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { IC ic2 = new; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

TEST(InterfaceClassCastingElaboration, ConstructingAnInterfaceClassIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class PutImp #(type PUT_T = logic); pure virtual function "
      "void put(PUT_T a); endclass\n"
      "interface class A; endclass\n"
      "module m;\n"
      "  PutImp#(int) put_ref;\n"
      "  A a;\n"
      "  initial begin\n"
      "    put_ref = new();\n"
      "    a = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {7, 8}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot construct object of interface class", kLine, "8.26.5"))
        << kLine;
  }
}

const char* const kInterfaceSpecializationAssignmentSrc =
    "interface class PutImp #(type PUT_T = logic); pure virtual function void "
    "put(PUT_T a); endclass\n"
    "class CI implements PutImp#(int);\n"
    "  virtual function void put(int a); endfunction\n"
    "endclass\n"
    "module m;\n"
    "  CI ci;\n"
    "  PutImp#(int) pi;\n"
    "  PutImp#(byte) pb;\n"
    "  PutImp pl;\n"
    "  initial begin\n"
    "    ci = new;\n"
    "    pi = ci;\n"
    "    pb = ci;\n"
    "    pl = ci;\n"
    "  end\n"
    "endmodule\n";

TEST(InterfaceClassCastingElaboration,
     HandleAssignsToTheSpecializationItImplements) {
  ElabFixture f;
  ElaborateSrc(kInterfaceSpecializationAssignmentSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {12}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(InterfaceClassCastingElaboration,
     DISABLED_HandleAssignedToAnotherSpecializationIsReported) {
  ElabFixture f;
  ElaborateSrc(kInterfaceSpecializationAssignmentSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {13, 14}) {
    EXPECT_TRUE(ReportedError(
        diags, "class handle assignment requires assignment compatible types",
        kLine, "8.4"))
        << kLine;
  }
}

}  // namespace
