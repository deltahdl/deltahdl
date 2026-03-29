#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InterfaceClassRandomizeParsing, ConstraintBlockInInterfaceClassParses) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "  constraint c { }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

TEST(InterfaceClassRandomizeParsing, CovergroupInInterfaceClassParses) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
               "  pure virtual function void foo();\n"
               "  covergroup cg; endgroup\n"
               "endclass\n"));
}

TEST(InterfaceClassRandomizeParsing, RandomizeCallOnInterfaceHandle) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
               "  pure virtual function void foo();\n"
               "endclass\n"
               "class C implements IC;\n"
               "  rand int x;\n"
               "  virtual function void foo();\n"
               "  endfunction\n"
               "endclass\n"
               "module m;\n"
               "  initial begin\n"
               "    C obj = new;\n"
               "    IC iref = obj;\n"
               "    void'(iref.randomize());\n"
               "  end\n"
               "endmodule\n"));
}

TEST(InterfaceClassRandomizeParsing, RandomizeWithInlineConstraintOnHandle) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
               "  pure virtual function void foo();\n"
               "endclass\n"
               "class C implements IC;\n"
               "  rand int x;\n"
               "  virtual function void foo();\n"
               "  endfunction\n"
               "endclass\n"
               "module m;\n"
               "  initial begin\n"
               "    C obj = new;\n"
               "    IC iref = obj;\n"
               "    void'(iref.randomize() with { });\n"
               "  end\n"
               "endmodule\n"));
}

TEST(InterfaceClassRandomizeParsing, PreRandomizeInImplementingClass) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "  function void pre_randomize();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  ASSERT_GE(cls->members.size(), 2u);
}

TEST(InterfaceClassRandomizeParsing, PostRandomizeInImplementingClass) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "  function void post_randomize();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  ASSERT_GE(cls->members.size(), 2u);
}

}  // namespace
