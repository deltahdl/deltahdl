#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassSyntaxElaboration, AnOverrideSpecifierInAnInterfaceClassIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class I;\n"
      "  pure virtual function :initial void f1();\n"
      "  pure virtual function :extends void f2();\n"
      "  pure virtual function :final void f3();\n"
      "  pure virtual function :initial :final void f4();\n"
      "  pure virtual task :initial t1();\n"
      "  pure virtual task :extends t2();\n"
      "  pure virtual task :final t3();\n"
      "endclass\n"
      "interface class J extends I;\n"
      "  pure virtual function :initial void g();\n"
      "endclass\n"
      "interface class K #(type T = int);\n"
      "  pure virtual function :extends T h();\n"
      "endclass\n"
      "package p;\n"
      "  interface class L; pure virtual task :initial u(); endclass\n"
      "endpackage\n"
      "module m;\n"
      "  interface class N; pure virtual function :final void v(); endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {2u, 3u, 4u, 5u, 6u, 7u, 8u, 11u, 14u, 17u, 20u}) {
    EXPECT_TRUE(ReportedError(diags,
                              "dynamic_override_specifiers shall not be used "
                              "in an interface class",
                              line, "8.26.1"))
        << line;
  }
  for (uint32_t line : {4u, 5u, 8u, 20u}) {
    EXPECT_TRUE(ReportedError(
        diags, "':final' shall not be specified on a pure virtual method", line,
        "8.20"))
        << line;
  }
}

TEST(ClassSyntaxElaboration, AnOverrideSpecifierOutsideAnInterfaceClassStands) {
  ElabFixture f;
  ElaborateSrc(
      "virtual class B;\n"
      "  virtual function void f2(); endfunction\n"
      "  virtual task t2(); endtask\n"
      "endclass\n"
      "virtual class V extends B;\n"
      "  pure virtual function :initial void f1();\n"
      "  pure virtual task :extends t2();\n"
      "endclass\n"
      "interface class I; pure virtual function void f(); endclass\n"
      "class C extends B implements I;\n"
      "  virtual function :initial void f(); endfunction\n"
      "  virtual function :extends :final void f2(); endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(ClassSyntaxElaboration,
     AFinalSpecifierOnAPureMethodOrConstraintIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "virtual class B;\n"
      "  rand int x;\n"
      "  constraint c2 { x > 0; }\n"
      "  virtual function void f2(); endfunction\n"
      "endclass\n"
      "virtual class V extends B;\n"
      "  pure virtual function :initial :final void f1();\n"
      "  pure virtual function :extends :final void f2();\n"
      "  pure virtual task :final t1();\n"
      "  pure constraint :final c1;\n"
      "  pure constraint :initial :final c3;\n"
      "  pure constraint :extends :final c2;\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(
        diags, "':final' shall not be specified on a pure virtual method", line,
        "8.20"))
        << line;
  }
  for (uint32_t line : {10u, 11u, 12u}) {
    EXPECT_TRUE(ReportedError(
        diags, "':final' shall not be specified on a pure constraint", line,
        "18.5.2"))
        << line;
  }
}

TEST(ClassSyntaxElaboration,
     AFinalSpecifierOnAMethodOrConstraintWithABodyStands) {
  ElabFixture f;
  ElaborateSrc(
      "virtual class B;\n"
      "  rand int x;\n"
      "  constraint c2 { x > 0; }\n"
      "  virtual function void f2(); endfunction\n"
      "endclass\n"
      "virtual class V extends B;\n"
      "  pure virtual function :initial void f1();\n"
      "  virtual function :extends :final void f2(); endfunction\n"
      "  virtual task :final t1(); endtask\n"
      "  pure constraint :initial c1;\n"
      "  constraint :extends :final c2 { x < 9; }\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
