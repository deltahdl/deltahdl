

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA82662, InterfaceExtendsMultipleWithTypedefOk) {
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

}  // namespace
