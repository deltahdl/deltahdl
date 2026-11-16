#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrePostRandomizePrototype, ConformingOverridesOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void pre_randomize(); endfunction\n"
             "  function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PrePostRandomizePrototype, NonVoidPreRandomizeError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int pre_randomize(); return 0; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'pre_randomize' shall have a void return type", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, NonVoidPostRandomizeError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int post_randomize(); return 0; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'post_randomize' shall have a void return type", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, PreRandomizeWithArgError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function void pre_randomize(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'pre_randomize' shall take no arguments", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, PostRandomizeWithArgError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function void post_randomize(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'post_randomize' shall take no arguments", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, PreRandomizeTaskFormError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  task pre_randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'pre_randomize' shall be a void function taking "
                            "no arguments, not a task",
                            2, "18.6.2"));
}

TEST(PrePostRandomizePrototype, PostRandomizeTaskFormError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  task post_randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'post_randomize' shall be a void function taking "
                            "no arguments, not a task",
                            2, "18.6.2"));
}

void ExpectPrototypeReported(const char* src, const char* message,
                             uint32_t line) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "18.6.2"));
}

TEST(PrePostRandomizePrototype, ImplicitReturnTypeError) {
  ExpectPrototypeReported(
      "class C;\n"
      "  function post_randomize(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "'post_randomize' shall have a void return type", 2);
}

TEST(PrePostRandomizePrototype, FormalWithADefaultValueError) {
  ExpectPrototypeReported(
      "class C;\n"
      "  function void pre_randomize(int a = 0); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "'pre_randomize' shall take no arguments", 2);
}

TEST(PrePostRandomizePrototype, ConformingExternPrototypesOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern function void pre_randomize();\n"
             "  extern function void post_randomize();\n"
             "endclass\n"
             "function void C::pre_randomize(); endfunction\n"
             "function void C::post_randomize(); endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PrePostRandomizePrototype, NonVoidExternPrototypeError) {
  ExpectPrototypeReported(
      "class C;\n"
      "  rand int x;\n"
      "  extern function int pre_randomize();\n"
      "endclass\n"
      "function int C::pre_randomize(); return 0; endfunction\n"
      "module m;\n"
      "endmodule\n",
      "'pre_randomize' shall have a void return type", 3);
}

TEST(PrePostRandomizePrototype, NonVoidInAPackageClassError) {
  ExpectPrototypeReported(
      "package p;\n"
      "  class C;\n"
      "    function int post_randomize(); return 0; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      "'post_randomize' shall have a void return type", 3);
}

TEST(PrePostRandomizePrototype, NonVoidInAModuleClassError) {
  ExpectPrototypeReported(
      "module m;\n"
      "  class C;\n"
      "    function int pre_randomize(); return 0; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      "'pre_randomize' shall have a void return type", 3);
}

TEST(PrePostRandomizePrototype, ArgumentInAProgramClassError) {
  ExpectPrototypeReported(
      "program p;\n"
      "  class C;\n"
      "    function void post_randomize(int a); endfunction\n"
      "  endclass\n"
      "endprogram\n",
      "'post_randomize' shall take no arguments", 3);
}

TEST(PrePostRandomizePrototype, NonVoidInADerivedClassError) {
  ExpectPrototypeReported(
      "class B;\n"
      "  function void pre_randomize(); endfunction\n"
      "endclass\n"
      "class D extends B;\n"
      "  function int pre_randomize(); return 0; endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "'pre_randomize' shall have a void return type", 5);
}

TEST(PrePostRandomizePrototype, ConformingInADerivedClassOk) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  function void pre_randomize(); endfunction\n"
             "endclass\n"
             "class D extends B;\n"
             "  function void pre_randomize(); super.pre_randomize(); "
             "endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PrePostRandomizePrototype, NonVoidInAnInterfaceClassError) {
  ExpectPrototypeReported(
      "interface class I;\n"
      "  pure virtual function int post_randomize();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "'post_randomize' shall have a void return type", 2);
}

TEST(PrePostRandomizePrototype, NonVoidPureVirtualPrototypeError) {
  ExpectPrototypeReported(
      "virtual class V;\n"
      "  pure virtual function int pre_randomize();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "'pre_randomize' shall have a void return type", 2);
}

}  // namespace
