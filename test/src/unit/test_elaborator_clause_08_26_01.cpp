#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassImplElaboration, InterfaceClassDeclOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void do_thing();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplElaboration, ParameterPortListOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC #(type T = logic, int W = 8);\n"
             "  pure virtual function T get();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplElaboration, EndclassLabelOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void f();\n"
             "endclass : IC\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplElaboration, AllValidItemTypesOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void f();\n"
             "  pure virtual task t();\n"
             "  typedef int my_int;\n"
             "  localparam int LP = 5;\n"
             "  parameter int W = 8;\n"
             "  ;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplElaboration, ParameterBodyItemIsLocalparamOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  parameter int WIDTH = 8;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplElaboration, ExtendsMultipleInterfacesOk) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
