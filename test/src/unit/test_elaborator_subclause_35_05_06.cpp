#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DpiExportFormalType, ExportedFunctionWithDynamicArrayArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int data[]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_take' has a dynamic "
                            "array formal argument and therefore cannot be "
                            "exported for DPI",
                            4, "35.5.6"));
}

TEST(DpiExportFormalType, ExportedTaskWithDynamicArrayArgSaysTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_consume(input byte stream[]); endtask
      export "DPI-C" task sv_consume;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 'sv_consume' has a dynamic "
                            "array formal argument and therefore cannot be "
                            "exported for DPI",
                            4, "35.5.6"));
}

TEST(DpiExportFormalType, ExportedFunctionWithFixedUnpackedArrayArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int data[4]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportFormalType, ExportedFunctionWithScalarArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int value); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportFormalType,
     ExportedFunctionWithDynamicArrayArgAmongOthersIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int ok, input int data[]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_take' has a dynamic "
                            "array formal argument and therefore cannot be "
                            "exported for DPI",
                            4, "35.5.6"));
}

TEST(DpiExportFormalType, ExportedFunctionWithEventArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_notify(input event ev); endfunction
      export "DPI-C" function sv_notify;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_notify' has a formal "
                            "argument 'ev' whose type is not permitted for DPI",
                            4, "35.5.6"));
}

TEST(DpiExportFormalType, ExportedTaskWithEventArgSaysTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_wait(input event ev); endtask
      export "DPI-C" task sv_wait;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 'sv_wait' has a formal "
                            "argument 'ev' whose type is not permitted for DPI",
                            4, "35.5.6"));
}

TEST(DpiExportFormalType, ExportedFunctionWithUnpackedUnionArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input union { byte b; int i; } u); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "SystemVerilog function 'sv_take' has an unpacked union "
                    "formal argument 'u'; only the packed form of a union is "
                    "permitted for DPI",
                    4, "35.5.6"));
}

TEST(DpiExportFormalType, ExportedFunctionWithPackedUnionArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(
          input union packed { bit [7:0] a; logic [7:0] b; } u);
      endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportFormalType, ExportedFunctionWithTypedefOfEventIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef event ev_t;
      function void sv_notify(input ev_t ev); endfunction
      export "DPI-C" function sv_notify;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_notify' has a formal "
                            "argument 'ev' whose type is not permitted for DPI",
                            5, "35.5.6"));
}

TEST(DpiImportFormalTypedefType, ImportedFunctionWithTypedefOfEventIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef event ev_t;
      import "DPI-C" function void f(input ev_t ev);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument 'ev' has type 'ev_t', which is "
                            "not permitted for a DPI imported subroutine",
                            4, "35.5.6"));
}

TEST(DpiImportFormalTypedefType,
     ImportedFunctionWithTypedefOfUnpackedUnionIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef union { byte b; int i; } u_t;
      import "DPI-C" function void f(input u_t u);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument 'u' has type 'u_t', an unpacked "
                            "union, which is not permitted for a DPI imported "
                            "subroutine; only the packed form of a union is "
                            "allowed",
                            4, "35.5.6"));
}

TEST(DpiImportFormalTypedefType, ImportedFunctionWithTypedefOfIntIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef int my_int_t;
      import "DPI-C" function void f(input my_int_t v);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiImportFormalTypedefType,
     ImportedFunctionWithWildcardImportedTypedefOfEventIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      typedef event ev_t;
    endpackage
    module m;
      import p::*;
      import "DPI-C" function void f(input ev_t ev);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument 'ev' has type 'ev_t', which is "
                            "not permitted for a DPI imported subroutine",
                            7, "35.5.6"));
}

TEST(DpiImportFormalTypedefType,
     ImportedFunctionWithNamedImportedTypedefOfEventIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      typedef event ev_t;
    endpackage
    module m;
      import p::ev_t;
      import "DPI-C" function void f(input ev_t ev);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument 'ev' has type 'ev_t', which is "
                            "not permitted for a DPI imported subroutine",
                            7, "35.5.6"));
}

TEST(DpiImportFormalTypedefType,
     ImportedFunctionWithWildcardImportedTypedefOfIntIsOk) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      typedef int my_int_t;
    endpackage
    module m;
      import p::*;
      import "DPI-C" function void f(input my_int_t v);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiImportFormalType, ImportedFunctionWithQueueFormalIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int f(input int a [$]);
      int q [$];
      initial $display("%0d", f(q));
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument 'a' of a DPI imported subroutine "
                            "has a queue dimension, which is not a permitted "
                            "formal argument type",
                            3, "35.5.6"));
}

TEST(DpiImportFormalType, ImportedFunctionWithAssociativeFormalIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int f(input int a [string]);
      int aa [string];
      initial $display("%0d", f(aa));
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument 'a' of a DPI imported subroutine "
                            "has an associative dimension, which is not a "
                            "permitted formal argument type",
                            3, "35.5.6"));
}

TEST(DpiImportFormalType, ImportedFunctionWithSizedAndOpenFormalsIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      parameter int N = 4;
      import "DPI-C" function int f(input int a [8], input int b [N],
                                    input int c []);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DpiExportFormalType, ExportedFunctionWithQueueFormalIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int f(input int a [$]);
        return a.size();
      endfunction
      export "DPI-C" function f;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'f' has a formal argument "
                            "'a' with a queue dimension, which is not a "
                            "permitted formal argument type for DPI",
                            6, "35.5.6"));
}

TEST(DpiExportFormalType, ExportedTaskWithAssociativeFormalIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task t(input int a [string]);
      endtask
      export "DPI-C" task t;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 't' has a formal argument 'a' "
                            "with an associative dimension, which is not a "
                            "permitted formal argument type for DPI",
                            5, "35.5.6"));
}

}  // namespace
