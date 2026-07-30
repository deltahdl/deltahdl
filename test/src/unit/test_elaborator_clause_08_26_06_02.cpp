

#include <string>

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

// Same rule, but the colliding value parameter is declared in the
// parameter_port_list (§8.25 form) rather than the class body. IA and IB each
// expose a port-list parameter W; IC inherits the name from both interface
// classes and supplies no override, so the unresolved collision is an error --
// the rule applies to the port-list declaration position as well as the body.
TEST(InterfaceClassParamTypeConflict,
     PortListParamCollisionFromTwoParentsError) {
  EXPECT_FALSE(
      ElabOk("interface class IA #(int W = 1);\n"
             "endclass\n"
             "interface class IB #(int W = 2);\n"
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

// The LRM example itself, but with the resolving typedef removed. The type
// parameter T is a port-list type parameter of both PutImp and GetImp and is
// bound through `extends ...#(TYPE)`; per the clause the mere name collision
// must be resolved even though PutImp::T and GetImp::T are compatible and T is
// never used by the subclass. Without the override an error shall occur.
TEST(InterfaceClassParamTypeConflict,
     LrmExampleTypeParamCollisionUnresolvedError) {
  EXPECT_FALSE(
      ElabOk("interface class PutImp#(type T = logic);\n"
             "  pure virtual function void put(T a);\n"
             "endclass\n"
             "interface class GetImp#(type T = logic);\n"
             "  pure virtual function T get();\n"
             "endclass\n"
             "interface class PutGetIntf#(type TYPE = logic)\n"
             "    extends PutImp#(TYPE), GetImp#(TYPE);\n"
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

// The simplest form of the rule: a class implementing a parameterized
// interface class directly. Specializing PutImp with `int` binds its formal T
// to int, so the inherited prototype is put(int) and a put(int) implements it.
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

// §8.26.6.2's own example. A class implementing PutGetIntf#(int) gives the type
// argument two steps to travel: `int` binds PutGetIntf's TYPE, and PutGetIntf
// passes TYPE on to PutImp and GetImp, whose own formal T it binds in turn, so
// the inherited prototypes are put(int) and int get().
//
// The implementing class is written once, with the type of put's argument left
// open, because that argument type is the whole of the difference between the
// case the standard accepts and the case it rejects. Spelling both classes out
// would leave the reader to find the one differing word.
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

// put(int) is the prototype the specialization produces, so Fifo implements it.
TEST(InterfaceClassParamTypeConflict,
     ImplMatchesPrototypeInheritedThroughSpec) {
  EXPECT_TRUE(ElabOk(FifoWithPutArg("int")));
}

// The control the accepting cases need. put(string) is not the prototype the
// specialization produces, so Fifo does not implement it and the class is in
// error. Without this case an elaborator that answered "compatible" to every
// comparison would pass every accepting test here, and the substitution they
// are meant to demonstrate would go unmeasured.
TEST(InterfaceClassParamTypeConflict, ImplArgTypeMustMatchTheSubstitutedOne) {
  EXPECT_FALSE(ElabOk(FifoWithPutArg("string")));
}

}  // namespace
