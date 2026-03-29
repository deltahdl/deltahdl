// §8.26.6.2

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Req: A name collision will occur if the same name is inherited from different
// interface classes. The subclass shall provide declarations that override all
// such name collisions.

TEST(InterfaceClassParamTypeConflict, ParamCollisionFromTwoParentsError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
      "  parameter int P = 1;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 2;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict, TypedefCollisionFromTwoParentsError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
      "  typedef int T;\n"
      "endclass\n"
      "interface class IB;\n"
      "  typedef int T;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// Req: A conflict occurs despite the fact that the inherited values match.

TEST(InterfaceClassParamTypeConflict, ParamCollisionEvenWhenValuesMatchError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
      "  parameter int P = 5;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 5;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

TEST(InterfaceClassParamTypeConflict, TypedefCollisionEvenWhenTypesMatchError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
      "  typedef logic T;\n"
      "endclass\n"
      "interface class IB;\n"
      "  typedef logic T;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// Req: The subclass shall provide parameter and/or type declarations that
// override all such name collisions.

TEST(InterfaceClassParamTypeConflict, TypedefOverrideResolvesParamCollision) {
  EXPECT_TRUE(ElabOk(
      "interface class IA;\n"
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
  EXPECT_TRUE(ElabOk(
      "interface class IA;\n"
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
  EXPECT_TRUE(ElabOk(
      "interface class IA;\n"
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

// Req: LRM example -- PutGetIntf resolves T inherited from PutImp and GetImp.

TEST(InterfaceClassParamTypeConflict, LrmExamplePutGetIntfResolvesCollision) {
  EXPECT_TRUE(ElabOk(
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
      "module m;\n"
      "endmodule\n"));
}

// Req: All collisions must be resolved -- error if only some are overridden.

TEST(InterfaceClassParamTypeConflict, PartialOverrideStillError) {
  EXPECT_FALSE(ElabOk(
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
      "endmodule\n"));
}

// No collision when names are distinct across parents.

TEST(InterfaceClassParamTypeConflict, DistinctNamesNoCollision) {
  EXPECT_TRUE(ElabOk(
      "interface class IA;\n"
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

}  // namespace
