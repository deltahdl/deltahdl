#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassParsing, WeakReferenceDecl) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    weak_reference #(my_obj) wr;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakReferenceAsMember) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "class holder;\n"
              "  weak_reference #(my_obj) wr;\n"
              "endclass\n"));
}

TEST(ClassParsing, WeakReferenceAsFunctionArg) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  function void f(weak_reference #(my_obj) wr);\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakReferenceAsTaskArg) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  task t(weak_reference #(my_obj) wr);\n"
              "  endtask\n"
              "endmodule\n"));
}

}  // namespace
