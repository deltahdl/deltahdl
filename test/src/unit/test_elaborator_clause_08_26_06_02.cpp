#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.6.2: Interface extends two interfaces with different typedefs — OK
// if subclass resolves the conflict.
TEST(ElabA82662, InterfaceExtendsMultipleWithTypedefOk) {
  EXPECT_TRUE(ElabOk(
      "interface class PutImp;\n"
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

// §8.26.6.2: Interface class inherits from two — no conflict if no
// overlapping names.
TEST(ElabA82662, NoConflictNoOverlapOk) {
  EXPECT_TRUE(ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "interface class C extends A, B;\n"
      "  pure virtual function void fc();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
