

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassParamTypeConflict, ParamCollisionFromTwoParentsError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
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
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
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

TEST(InterfaceClassParamTypeConflict, ParamCollisionEvenWhenValuesMatchError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
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
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
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

TEST(InterfaceClassParamTypeConflict, PartialOverrideStillError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
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

// C1 edge: a parameter in one parent and a typedef of the same name in
// another parent still collide -- the conflict is on the name, regardless
// of whether the inherited declarations are of the same kind.
TEST(InterfaceClassParamTypeConflict, ParamVsTypedefCrossKindCollisionError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  parameter int N = 1;\n"
             "endclass\n"
             "interface class IB;\n"
             "  typedef int N;\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// C1 edge: the same name inherited from three different interface classes
// is still a single unresolved collision.
TEST(InterfaceClassParamTypeConflict, CollisionFromThreeParentsError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
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
             "endmodule\n"));
}

// C1 edge: a collision can arise transitively -- the same name reaches the
// subclass from two distinct ancestor interface classes through a
// multi-level extends chain (this is not a diamond: IA and IB are
// different source classes).
TEST(InterfaceClassParamTypeConflict,
     TransitiveCollisionFromDistinctAncestorsError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
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
             "endmodule\n"));
}

// C2 edge: an override in the subclass resolves a collision that arrives
// transitively through the extends chain.
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

}  // namespace
