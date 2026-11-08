#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassParamTypeConflict, ParamCollisionFromTwoParentsError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  parameter int P = 1;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 2;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 7,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, TypedefCollisionFromTwoParentsError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  typedef int T;\n"
      "endclass\n"
      "interface class IB;\n"
      "  typedef int T;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 7,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, ParamCollisionEvenWhenValuesMatchError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  parameter int P = 5;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 5;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 7,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict,
     PortListParamCollisionFromTwoParentsError) {
  ElabFixture f;
  ElabOk(
      "interface class IA #(int W = 1);\n"
      "endclass\n"
      "interface class IB #(int W = 2);\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 5,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, TypedefOverrideResolvesParamCollision) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  parameter int P = 1;\n"
             "endclass\n"
             "interface class IB;\n"
             "  parameter int P = 2;\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "  typedef int P;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict, ParamOverrideResolvesParamCollision) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  parameter int P = 1;\n"
             "endclass\n"
             "interface class IB;\n"
             "  parameter int P = 2;\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "  parameter int P = 10;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict, TypedefOverrideResolvesTypedefCollision) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  typedef int T;\n"
             "endclass\n"
             "interface class IB;\n"
             "  typedef int T;\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "  typedef logic T;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict, LrmExamplePutGetIntfResolvesCollision) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp#(type T = logic);\n"
             "  pure virtual function void put(T a);\n"
             "endclass\n"
             "interface class GetImp#(type T = logic);\n"
             "  pure virtual function T get();\n"
             "endclass\n"
             "interface class PutGetIntf#(type TYPE = logic)\n"
             "    extends PutImp#(TYPE), GetImp#(TYPE);\n"
             "  typedef TYPE T;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict,
     LrmExampleTypeParamCollisionUnresolvedError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp#(type T = logic);\n"
      "  pure virtual function void put(T a);\n"
      "endclass\n"
      "interface class GetImp#(type T = logic);\n"
      "  pure virtual function T get();\n"
      "endclass\n"
      "interface class PutGetIntf#(type TYPE = logic)\n"
      "    extends PutImp#(TYPE), GetImp#(TYPE);\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 7,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, PartialOverrideStillError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  parameter int P = 1;\n"
      "  parameter int Q = 2;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 3;\n"
      "  parameter int Q = 4;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "  parameter int P = 10;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 9,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, DistinctNamesNoCollision) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  parameter int P = 1;\n"
             "endclass\n"
             "interface class IB;\n"
             "  parameter int Q = 2;\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict, ParamVsTypedefCrossKindCollisionError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  parameter int N = 1;\n"
      "endclass\n"
      "interface class IB;\n"
      "  typedef int N;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 7,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, CollisionFromThreeParentsError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  parameter int P = 1;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 2;\n"
      "endclass\n"
      "interface class ID;\n"
      "  parameter int P = 3;\n"
      "endclass\n"
      "interface class IE extends IA, IB, ID;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 10,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict,
     TransitiveCollisionFromDistinctAncestorsError) {
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
      "  parameter int P = 1;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 2;\n"
      "endclass\n"
      "interface class IC extends IA;\n"
      "endclass\n"
      "interface class ID extends IC, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 9,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, TransitiveCollisionResolvedByOverride) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  parameter int P = 1;\n"
             "endclass\n"
             "interface class IB;\n"
             "  parameter int P = 2;\n"
             "endclass\n"
             "interface class IC extends IA;\n"
             "endclass\n"
             "interface class ID extends IC, IB;\n"
             "  parameter int P = 9;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict, ImplMatchesDirectlySpecializedPrototype) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp#(type T = logic);\n"
             "  pure virtual function void put(T a);\n"
             "endclass\n"
             "class Fifo implements PutImp#(int);\n"
             "  int store;\n"
             "  virtual function void put(int a);\n"
             "    store = a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

std::string FifoWithPutArg(const char* put_arg_type) {
  return std::string(
             "interface class PutImp#(type T = logic);\n"
             "  pure virtual function void put(T a);\n"
             "endclass\n"
             "interface class GetImp#(type T = logic);\n"
             "  pure virtual function T get();\n"
             "endclass\n"
             "interface class PutGetIntf#(type TYPE = logic)\n"
             "    extends PutImp#(TYPE), GetImp#(TYPE);\n"
             "  typedef TYPE T;\n"
             "endclass\n"
             "class Fifo implements PutGetIntf#(int);\n"
             "  int store;\n"
             "  virtual function void put(") +
         put_arg_type +
         " a);\n"
         "    store = 0;\n"
         "  endfunction\n"
         "  virtual function int get();\n"
         "    return store;\n"
         "  endfunction\n"
         "endclass\n"
         "module m;\n"
         "endmodule\n";
}

TEST(InterfaceClassParamTypeConflict,
     ImplMatchesPrototypeInheritedThroughSpec) {
  EXPECT_TRUE(ElabOk(FifoWithPutArg("int")));
}

TEST(InterfaceClassParamTypeConflict, ImplArgTypeMustMatchTheSubstitutedOne) {
  ElabFixture f;
  ElabOk(FifoWithPutArg("string"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not match signature of pure virtual method",
                            13, "8.26.6.1"));
}

TEST(InterfaceClassParamTypeConflict, ParamCollisionInsideAModuleError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class IA;\n"
      "    parameter int P = 1;\n"
      "    pure virtual function void fa();\n"
      "  endclass\n"
      "  interface class IB;\n"
      "    parameter int P = 2;\n"
      "    pure virtual function void fb();\n"
      "  endclass\n"
      "  interface class IC extends IA, IB;\n"
      "    pure virtual function void fc();\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 10,
      "8.26.6.2"));
}

TEST(InterfaceClassParamTypeConflict, DistinctParamNamesInsideAModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  interface class IA;\n"
             "    parameter int P = 1;\n"
             "    pure virtual function void fa();\n"
             "  endclass\n"
             "  interface class IB;\n"
             "    parameter int Q = 2;\n"
             "    pure virtual function void fb();\n"
             "  endclass\n"
             "  interface class IC extends IA, IB;\n"
             "    pure virtual function void fc();\n"
             "  endclass\n"
             "endmodule\n"));
}

}  // namespace
